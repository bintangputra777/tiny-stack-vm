// tiny-stack-vm-01: a complete interpreter for make.fun's tiny stack ISA (kit generator/subject/ISA.md),
// mirroring the reference VM (generator/subject/vm.mjs) exactly: its per-step check order and its own
// arithmetic expressions (Math.imul, (a / b) | 0, a % b, >>> for unsigned), bit for bit.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

function run(P, I) {
  const n = P.length, D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), buf = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const done = (code) => ({ out: buf.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = P[pc];
    steps++;
    switch (op) {
      case 0x00: return done(0);
      case 0x01:
        if (pc + 1 >= n) return done(9);
        if (sp === 256) return done(3);
        D[sp++] = (P[pc + 1] << 24) >> 24; pc += 2; break;
      case 0x02:
        if (pc + 4 >= n) return done(9);
        if (sp === 256) return done(3);
        D[sp++] = P[pc + 1] | (P[pc + 2] << 8) | (P[pc + 3] << 16) | (P[pc + 4] << 24); pc += 5; break;
      case 0x03:
        if (sp < 1) return done(2);
        sp--; pc++; break;
      case 0x04:
        if (sp < 1) return done(2);
        if (sp === 256) return done(3);
        D[sp] = D[sp - 1]; sp++; pc++; break;
      case 0x05: {
        if (sp < 2) return done(2);
        const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; pc++; break;
      }
      case 0x06:
        if (sp < 2) return done(2);
        if (sp === 256) return done(3);
        D[sp] = D[sp - 2]; sp++; pc++; break;
      case 0x07: {
        if (sp < 3) return done(2);
        const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; pc++; break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary ops ( a b -- r )
        if (sp < 2) return done(2);
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : a % b | 0; }
        else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return done(4); r = (a >>> 0) % (b >>> 0) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = a >>> 0 < b >>> 0 ? 1 : 0;
        D[sp - 2] = r; sp--; pc++; break;
      }
      case 0x17:
        if (sp < 1) return done(2);
        D[sp - 1] = -D[sp - 1] | 0; pc++; break;
      case 0x1b:
        if (sp < 1) return done(2);
        D[sp - 1] = ~D[sp - 1]; pc++; break;
      case 0x30:
        if (pc + 2 >= n) return done(9);
        pc = pc + 3 + (((P[pc + 1] | (P[pc + 2] << 8)) << 16) >> 16); break;
      case 0x31: case 0x32: {
        if (pc + 2 >= n) return done(9);
        if (sp < 1) return done(2);
        const v = D[--sp], rel = ((P[pc + 1] | (P[pc + 2] << 8)) << 16) >> 16;
        pc = pc + 3 + ((op === 0x31) === (v === 0) ? rel : 0); break;
      }
      case 0x33:
        if (pc + 2 >= n) return done(9);
        if (csp === 64) return done(7);
        C[csp++] = pc + 3; pc = P[pc + 1] | (P[pc + 2] << 8); break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = C[--csp]; break;
      case 0x40: {
        if (sp < 1) return done(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        D[sp - 1] = M[a]; pc++; break;
      }
      case 0x41: {
        if (sp < 2) return done(2);
        const a = D[sp - 1];
        if (a < 0 || a > 255) return done(6);
        M[a] = D[sp - 2]; sp -= 2; pc++; break;
      }
      case 0x50: {
        if (sp < 1) return done(2);
        const s = String(D[sp - 1]);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let k = 0; k < s.length; k++) buf[olen++] = s.charCodeAt(k);
        pc++; break;
      }
      case 0x51:
        if (sp < 1) return done(2);
        if (olen === 65536) return done(11);
        buf[olen++] = D[--sp] & 255; pc++; break;
      case 0x52:
        if (sp === 256) return done(3);
        D[sp++] = ip < I.length ? I[ip++] : -1; pc++; break;
      case 0x53:
        if (sp < 1) return done(2);
        return done(D[sp - 1] & 255);
      default: return done(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
