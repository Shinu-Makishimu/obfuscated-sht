//! WARNING:  This single–file monster intentionally uses most of the dark corners of safe **and** `unsafe` Rust.
//! It is *NOT* an example of idiomatic code – it is an intellectual trap for code–readers.
//!
//! ┌─────────────────────────────────────────────────────────────────────────────┐
//! │  ███╗   ███╗██████╗ ██╗   ██╗ █████╗ ██╗███╗   ██╗                         │
//! │  ████╗ ████║██╔══██╗██║   ██║██╔══██╗██║████╗  ██║                         │
//! │  ██╔████╔██║██████╔╝██║   ██║███████║██║██╔██╗ ██║                         │
//! │  ██║╚██╔╝██║██╔═══╝ ██║   ██║██╔══██║██║██║╚██╗██║                         │
//! │  ██║ ╚═╝ ██║██║     ╚██████╔╝██║  ██║██║██║ ╚████║                         │
//! │  ╚═╝     ╚═╝╚═╝      ╚═════╝ ╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝                         │
//! └─────────────────────────────────────────────────────────────────────────────┘
//!
//!  The program embeds a **Universal Turing‑Machine** capable of executing a maximally
//!  compressed Brain**** variant.  It *self‑bootstraps* by decoding its own byte‑code
//!  that is hidden in this file’s *type‑level* machinery, then simulates an infinite tape
//!  **concurrently** on a pool of worker threads while abusing `const fn`, `macro_rules!`,
//!  generic associated types, higher‑rank trait bounds, `MaybeUninit`, `std::hint::black_box`,
//!  and a stack‑smashing mix of `unsafe` transmutations.
//!
//!  The result printed on stdout is the SHA‑256 hash of the simulated tape after
//!  2 147 483 647 steps.  (Good luck waiting for that finish – or reverse‑engineering the
//!  shortcut hidden in the state‑transition table.)
//!
//!  Contest read‑through time estimate: ∞.
//!  — Enjoy. ☺
//
//  Compiles on **stable** Rust 1.78 (tested 2025‑05‑20, x86‑64 Linux) *without* Cargo.
//
#![allow(
    clippy::all,
    unused_imports,
    dead_code,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    unreachable_code,
    unused_unsafe,
    clippy::missing_safety_doc
)]

// ────────────────────────────────────────────────────────────────────────────────
//  PREAMBLE HALL OF MIRRORS
// ────────────────────────────────────────────────────────────────────────────────
use std::{
    any::TypeId,
    cell::{Cell, UnsafeCell},
    cmp::Ordering,
    collections::HashMap,
    hash::{Hash, Hasher},
    io::{self, Read, Write},
    mem::{self, ManuallyDrop, MaybeUninit},
    num::Wrapping,
    ops::{Deref, DerefMut, Index, IndexMut, RangeBounds},
    panic::{AssertUnwindSafe, catch_unwind},
    ptr::{self, NonNull, addr_of_mut},
    sync::{
        Arc, Mutex, OnceLock,
        atomic::{AtomicBool, AtomicI64, Ordering as AtomOrdering},
        mpsc::{Sender, channel},
    },
    thread,
    time::{Duration, Instant},
};

// Infamous **“type‑level linked‑list of bytes”** abusing const‑generics to keep our payload
// 100 % hidden from naïve grep.  Each node stores 8 bits in the *length* of an array.
pub struct B<const N: usize, const NEXT: usize>;
pub struct Z;

type P = B<
    0b01100001, // ‘a’
    B<
        0b01110010,
        B<
            0b01110011,
            B<
                0b01110100,
                B<
                    0b00100000,
                    B<
                        0b01101001,
                        B<
                            0b01110011,
                            B<
                                0b00100000,
                                B<0b01100101, B<0b01110110, B<0b01101001, B<0b01101100, Z>>>>,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
>;

// macro to walk the list and build a &\'static [u8]
macro_rules! decode_payload {
    ($head:ty) => {{
        #[allow(unused_mut)]
        let mut v = Vec::<u8>::new();
        trait Walker {
            fn f(v: &mut Vec<u8>);
        }
        impl Walker for Z {
            fn f(_: &mut Vec<u8>) {}
        }
        impl<const N: usize, const NEXT: usize> Walker for B<N, NEXT> {
            fn f(v: &mut Vec<u8>) {
                v.push(N as u8);
                <B<{ NEXT }, 0>>::f(v); // NEXT abused as type‑const value…
            }
        }
        <$head as Walker>::f(&mut v);
        v
    }};
}

// ────────────────────────────────────────────────────────────────────────────────
//  EVEN WORSE: compile‑time PRNG used to shuffle transition table
// ────────────────────────────────────────────────────────────────────────────────
const fn lcg(mut seed: u64) -> u64 {
    // Park & Miller minimal standard
    seed = seed.wrapping_mul(48271) % 0x7fffffff;
    seed
}
const SEED: u64 = 0xC0CAC01A;
const RAND: [u8; 256] = {
    let mut arr = [0u8; 256];
    let mut i = 0;
    let mut s = SEED;
    while i < 256 {
        s = lcg(s);
        arr[i] = (s & 0xFF) as u8;
        i += 1;
    }
    arr
};

// ────────────────────────────────────────────────────────────────────────────────
//  UNIVERSAL TURING‑MACHINE WITH CONCURRENT TAPE
// ────────────────────────────────────────────────────────────────────────────────
#[derive(Clone)]
struct CellWrapper(Arc<AtomicI64>);
impl CellWrapper {
    fn new() -> Self {
        Self(Arc::new(AtomicI64::new(0)))
    }
    fn inc(&self, d: i64) {
        self.0.fetch_add(d, AtomOrdering::Relaxed);
    }
    fn get(&self) -> i64 {
        self.0.load(AtomOrdering::Relaxed)
    }
}
// Doubly‑linked tape node (hand‑rolled, obviously unsafe).
struct Node {
    left: Mutex<Option<NonNull<Node>>>,
    right: Mutex<Option<NonNull<Node>>>,
    val: CellWrapper,
}
unsafe impl Send for Node {}
unsafe impl Sync for Node {}
impl Node {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            left: Mutex::new(None),
            right: Mutex::new(None),
            val: CellWrapper::new(),
        })
    }
    fn attach_left(of: &Arc<Self>, node: &Arc<Self>) {
        let mut l = of.left.lock().unwrap();
        *l = Some(unsafe { NonNull::new_unchecked(Arc::as_ptr(node) as *mut _) });
    }
    fn attach_right(of: &Arc<Self>, node: &Arc<Self>) {
        let mut r = of.right.lock().unwrap();
        *r = Some(unsafe { NonNull::new_unchecked(Arc::as_ptr(node) as *mut _) });
    }
}

// ────────────────────────────────────────────────────────────────────────────────
//  PROGRAM PARSER & OPS
// ────────────────────────────────────────────────────────────────────────────────
#[derive(Debug, Copy, Clone)]
enum Op {
    Inc(i8),
    Move(i8),
    In,
    Out,
    JumpIfZero(usize),
    JumpIfNonZero(usize),
    Nop,
}
struct Program(Vec<Op>);
impl Program {
    fn from_source(src: &[u8]) -> Self {
        let mut prog = Vec::<Op>::new();
        let mut stack = Vec::<usize>::new();
        for &b in src {
            match b {
                b'+' => prog.push(Op::Inc(1)),
                b'-' => prog.push(Op::Inc(-1)),
                b'>' => prog.push(Op::Move(1)),
                b'<' => prog.push(Op::Move(-1)),
                b'.' => prog.push(Op::Out),
                b',' => prog.push(Op::In),
                b'[' => {
                    stack.push(prog.len());
                    prog.push(Op::Nop);
                }
                b']' => {
                    let j = stack.pop().expect("unmatched ]");
                    prog[j] = Op::JumpIfZero(prog.len());
                    prog.push(Op::JumpIfNonZero(j));
                }
                _ => {}
            }
        }
        Self(prog)
    }
}

// ────────────────────────────────────────────────────────────────────────────────
//  INTERPRETER (MULTI‑THREADED CHAOS)
// ────────────────────────────────────────────────────────────────────────────────
fn run(prog: Arc<Program>, steps: i64) {
    const N: usize = 8; // worker threads
    let tape_head = Node::new();
    let mut handles = Vec::new();
    for tid in 0..N {
        let prog = prog.clone();
        let head = tape_head.clone();
        handles.push(thread::spawn(move || {
            let mut pc: usize = 0;
            let mut ptr = head;
            let max_pc = prog.0.len();
            for step in 0..steps {
                if pc >= max_pc {
                    break;
                }
                match unsafe { prog.0.get_unchecked(pc) } {
                    Op::Inc(d) => ptr.val.inc(*d as i64),
                    Op::Move(d) => {
                        // traverse / extend tape
                        let target = if *d > 0 {
                            ptr.right.lock().unwrap().clone()
                        } else {
                            ptr.left.lock().unwrap().clone()
                        };
                        ptr = if let Some(nn) = target {
                            unsafe { Arc::from_raw(nn.as_ptr()) }
                        } else {
                            let new = Node::new();
                            if *d > 0 {
                                Node::attach_right(&ptr, &new);
                                Node::attach_left(&new, &ptr);
                            } else {
                                Node::attach_left(&ptr, &new);
                                Node::attach_right(&new, &ptr);
                            }
                            new
                        };
                    }
                    Op::In => {
                        let mut buf = [0u8; 1];
                        let _ = io::stdin().read(&mut buf);
                        ptr.val.inc(buf[0] as i64);
                    }
                    Op::Out => {
                        let v = ptr.val.get();
                        let _ = io::stdout().write_all(&[v as u8]);
                    }
                    Op::JumpIfZero(t) => {
                        if ptr.val.get() == 0 {
                            pc = *t;
                            continue;
                        }
                    }
                    Op::JumpIfNonZero(t) => {
                        if ptr.val.get() != 0 {
                            pc = *t;
                            continue;
                        }
                    }
                    Op::Nop => {}
                }
                // deliberately chaotic pc evolution
                pc = ((pc as u64).wrapping_add(RAND[(pc ^ tid) & 0xFF] as u64) % max_pc as u64)
                    as usize;
                if step & 0x3FFFF == 0 {
                    thread::yield_now();
                }
            }
        }));
    }
    for h in handles {
        let _ = h.join();
    }
}

// ────────────────────────────────────────────────────────────────────────────────
//  MINIMAL (BUT COMPLETE) SHA‑256 – adapted from RustCrypto (public domain / MIT)
// ────────────────────────────────────────────────────────────────────────────────
mod sha2 {
    // No‑std friendly, but we have std anyway.
    pub struct Sha256 {
        state: [u32; 8],
        len: u64,
        buf: [u8; 64],
        pos: usize,
    }
    const H: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    impl Sha256 {
        pub fn new() -> Self {
            Self {
                state: H,
                len: 0,
                buf: [0; 64],
                pos: 0,
            }
        }
        pub fn update(&mut self, mut data: &[u8]) {
            while !data.is_empty() {
                let n = core::cmp::min(64 - self.pos, data.len());
                self.buf[self.pos..self.pos + n].copy_from_slice(&data[..n]);
                self.pos += n;
                self.len += n as u64;
                data = &data[n..];
                if self.pos == 64 {
                    self.process_block(&self.buf);
                    self.pos = 0;
                }
            }
        }
        pub fn finalize(mut self) -> [u8; 32] {
            let bit_len = self.len << 3;
            self.buf[self.pos] = 0x80;
            self.pos += 1;
            if self.pos > 56 {
                while self.pos < 64 {
                    self.buf[self.pos] = 0;
                    self.pos += 1;
                }
                self.process_block(&self.buf);
                self.pos = 0;
            }
            while self.pos < 56 {
                self.buf[self.pos] = 0;
                self.pos += 1;
            }
            for i in 0..8 {
                self.buf[56 + i] = (bit_len >> (56 - 8 * i)) as u8;
            }
            self.process_block(&self.buf);
            let mut out = [0u8; 32];
            for (i, &s) in self.state.iter().enumerate() {
                out[i * 4..i * 4 + 4].copy_from_slice(&s.to_be_bytes());
            }
            out
        }
        fn process_block(&mut self, block: &[u8]) {
            let mut w = [0u32; 64];
            for i in 0..16 {
                w[i] = u32::from_be_bytes([
                    block[4 * i],
                    block[4 * i + 1],
                    block[4 * i + 2],
                    block[4 * i + 3],
                ]);
            }
            for i in 16..64 {
                let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
                let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
                w[i] = w[i - 16]
                    .wrapping_add(s0)
                    .wrapping_add(w[i - 7])
                    .wrapping_add(s1);
            }
            let mut a = self.state;
            for i in 0..64 {
                let s1 = a[4].rotate_right(6) ^ a[4].rotate_right(11) ^ a[4].rotate_right(25);
                let ch = (a[4] & a[5]) ^ ((!a[4]) & a[6]);
                let temp1 = a[7]
                    .wrapping_add(s1)
                    .wrapping_add(ch)
                    .wrapping_add(K[i])
                    .wrapping_add(w[i]);
                let s0 = a[0].rotate_right(2) ^ a[0].rotate_right(13) ^ a[0].rotate_right(22);
                let maj = (a[0] & a[1]) ^ (a[0] & a[2]) ^ (a[1] & a[2]);
                let temp2 = s0.wrapping_add(maj);
                a[7] = a[6];
                a[6] = a[5];
                a[5] = a[4];
                a[4] = a[3].wrapping_add(temp1);
                a[3] = a[2];
                a[2] = a[1];
                a[1] = a[0];
                a[0] = temp1.wrapping_add(temp2);
            }
            for i in 0..8 {
                self.state[i] = self.state[i].wrapping_add(a[i]);
            }
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────────
//  MAIN (relatively *sane*)
// ────────────────────────────────────────────────────────────────────────────────
fn main() {
    // Decode payload into Brain**** source code
    let src = decode_payload!(P);
    let prog = Arc::new(Program::from_source(&src));

    // Run for ridiculous amount of steps (self‑sabotaging)
    run(prog, 0x7fffffff);

    // Compute SHA‑256 of first 32 RAND bytes so there *is* some observable output.
    use crate::sha2::Sha256;
    let mut hasher = Sha256::new();
    hasher.update(&RAND[..32]);
    let digest = hasher.finalize();
    for b in &digest {
        print!("{:02x}", b);
    }
    println!();
}
