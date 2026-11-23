// Tiny stack VM (kit ISA.md): wrapping 32-bit ints, traps per spec.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Instruction facts indexed by opcode byte: immediate bytes after the
// opcode, values popped, and net stack change (pushes - pops). NEED stays
// -1 for a byte no opcode names, which is how trap 5 is told apart.
const IMM = new Uint8Array(256);
const NEED = new Int16Array(256).fill(-1);
const NET = new Int16Array(256);
const D = (op: number, imm: number, pops: number, pushes: number): void => {
  IMM[op] = imm; NEED[op] = pops; NET[op] = pushes - pops;
};
D(0, 0, 0, 0); D(1, 1, 0, 1); D(2, 4, 0, 1); D(3, 0, 1, 0); D(4, 0, 1, 2);
D(5, 0, 2, 2); D(6, 0, 2, 3); D(7, 0, 3, 3);
for (let op = 16; op <= 34; op++) D(op, 0, 2, 1); // the binary group, 0x10-0x22
D(23, 0, 1, 1); D(27, 0, 1, 1); // NEG, NOT: unary, inside that range
D(48, 2, 0, 0); D(49, 2, 1, 0); D(50, 2, 1, 0); D(51, 2, 0, 0); D(52, 0, 0, 0);
D(64, 0, 1, 1); D(65, 0, 2, 0); D(80, 0, 1, 0); D(81, 0, 1, 0); D(82, 0, 0, 1);
D(83, 0, 1, 0);

const STACK_MAX = 256, CALLS_MAX = 64, MEM_WORDS = 256;
const STEP_LIMIT = 1000000, OUTPUT_MAX = 65536, INT_MIN = -2147483648;

// Runs one program: returns its output bytes and exit code.
function execute(prog: Uint8Array, input: Uint8Array): { bytes: Uint8Array; code: number } {
  const stack = new Int32Array(STACK_MAX);
  const calls = new Int32Array(CALLS_MAX);
  const mem = new Int32Array(MEM_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  const n = prog.length;
  let sp = 0, csp = 0, pc = 0, steps = 0, olen = 0, ipos = 0;
  const end = (code: number) => ({ bytes: out.subarray(0, olen), code });

  for (;;) {
    // One step, in the ISA's order of checks.
    if (steps >= STEP_LIMIT) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const need = NEED[op];
    if (need < 0) return end(5);
    const imm = IMM[op];
    if (pc + imm >= n) return end(9);
    steps++;
    if (sp < need) return end(2);
    if (sp + NET[op] > STACK_MAX) return end(3);
    const at = pc + 1; // the immediate's first byte
    pc = at + imm; // the next instruction, unless a jump moves pc

    // The binary group shares one shape: pop b, pop a, push one result.
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b) {
      const b = stack[sp - 1], a = stack[sp - 2];
      let r: number;
      // ADD SUB MUL DIV MOD DIVU MODU AND OR XOR SHL SHR SHRU EQ LT LTU.
      // MUL is the exact low 32 bits; DIV truncates toward zero; MOD takes
      // the sign of a; the U forms read unsigned; shifts use b's low 5 bits.
      switch (op) {
        case 0x10: r = (a + b) | 0; break;
        case 0x11: r = (a - b) | 0; break;
        case 0x12: r = Math.imul(a, b); break;
        case 0x13:
          if (b === 0) return end(4);
          r = a === INT_MIN && b === -1 ? a : (a / b) | 0; break;
        case 0x14:
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0; break;
        case 0x15:
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
        case 0x16:
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; break;
        case 0x18: r = a & b; break;
        case 0x19: r = a | b; break;
        case 0x1a: r = a ^ b; break;
        case 0x1c: r = a << (b & 31); break;
        case 0x1d: r = a >> (b & 31); break;
        case 0x1e: r = (a >>> (b & 31)) | 0; break;
        case 0x20: r = a === b ? 1 : 0; break;
        case 0x21: r = a < b ? 1 : 0; break;
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
      }
      stack[sp - 2] = r; sp--;
      continue;
    }

    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: stack[sp++] = (prog[at] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: // PUSH32, little-endian
        stack[sp++] = prog[at] | (prog[at + 1] << 8) | (prog[at + 2] << 16) | (prog[at + 3] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break; // DUP
      case 0x05: { // SWAP
        const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; break;
      }
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = -stack[sp - 1] | 0; break; // NEG, wraps
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: signed offset from next
        const off = ((prog[at] | (prog[at + 1] << 8)) << 16) >> 16;
        let go = op === 0x30;
        if (!go) { const v = stack[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
        if (go) pc += off;
        break;
      }
      case 0x33: // CALL: the immediate is an absolute address
        if (csp >= CALLS_MAX) return end(7);
        calls[csp++] = pc; pc = prog[at] | (prog[at + 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return end(8);
        pc = calls[--csp];
        break;
      case 0x40: { // LOAD
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return end(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEM_WORDS) return end(6);
        mem[addr] = stack[sp - 2]; sp -= 2;
        break;
      }
      case 0x50: { // PRINT: the value in decimal ASCII, no newline
        const s = String(stack[sp - 1]);
        if (olen + s.length > OUTPUT_MAX) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC: one byte, the value's low 8 bits
        if (olen >= OUTPUT_MAX) return end(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52: // IN: -1 once the input is used up
        stack[sp++] = ipos < input.length ? input[ipos++] : -1;
        break;
      case 0x53: return end(stack[sp - 1] & 255); // EXIT: the code's low byte
      default: return end(5); // unreachable
    }
  }
}

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const prog = new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin')));
  const inp = new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin')));
  const { bytes, code } = execute(prog, inp);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), `${code}\n`);
}
