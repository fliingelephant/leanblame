/-
SHA-256 (FIPS 180-4) in pure Lean. Lean core ships no SHA-256, and every hash
LeanBlame publishes (claim hashes, export and boundary-list hashes, record file
names) is a SHA-256 digest.
-/

namespace LeanBlame.Sha256

private def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def h0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Incremental hashing state. -/
structure State where
  h : Array UInt32 := h0
  /-- Bytes not yet forming a full 64-byte block. -/
  pending : ByteArray := ByteArray.empty
  /-- Total message length in bytes. -/
  length : Nat := 0

/-- Compress the 64-byte block of `data` starting at `off` into `h`. -/
private def compress (h : Array UInt32) (data : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b0 := data.get! (off + 4*i)
    let b1 := data.get! (off + 4*i + 1)
    let b2 := data.get! (off + 4*i + 2)
    let b3 := data.get! (off + 4*i + 3)
    w := w.push ((b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32)
  for i in [16:64] do
    let w15 := w[i-15]!
    let w2 := w[i-2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
    let t1 := hh + S1 + ch + k[i]! + w[i]!
    let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := S0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Feed bytes into the state. -/
def State.update (s : State) (bytes : ByteArray) : State := Id.run do
  let data := s.pending ++ bytes
  let mut h := s.h
  let mut off := 0
  while off + 64 ≤ data.size do
    h := compress h data off
    off := off + 64
  return { h, pending := data.extract off data.size, length := s.length + bytes.size }

/-- Finish hashing and return the 32-byte digest. -/
def State.finish (s : State) : ByteArray := Id.run do
  let bitLen := s.length * 8
  let mut tail := s.pending.push 0x80
  while tail.size % 64 != 56 do
    tail := tail.push 0
  for i in [0:8] do
    tail := tail.push ((bitLen >>> (8 * (7 - i))) % 256).toUInt8
  let mut h := s.h
  let mut off := 0
  while off + 64 ≤ tail.size do
    h := compress h tail off
    off := off + 64
  let mut out := ByteArray.empty
  for word in h do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase hexadecimal rendering of a byte array. -/
def toHex (bytes : ByteArray) : String := Id.run do
  let mut s := ""
  for b in bytes do
    s := s.push (hexDigit (b >>> 4))
    s := s.push (hexDigit (b &&& 0xf))
  return s

/-- Lowercase hex SHA-256 of a byte array. -/
def hexOfBytes (bytes : ByteArray) : String :=
  toHex (({} : State).update bytes).finish

/-- Lowercase hex SHA-256 of the UTF-8 encoding of a string. -/
def hexOfString (s : String) : String :=
  hexOfBytes s.toUTF8

/-- Lowercase hex SHA-256 of a file, read in chunks. -/
partial def hexOfFile (path : System.FilePath) : IO String := do
  let h ← IO.FS.Handle.mk path .read
  let rec go (s : State) : IO State := do
    let chunk ← h.read (1024 * 1024)
    if chunk.isEmpty then return s else go (s.update chunk)
  return toHex (← go {}).finish

end LeanBlame.Sha256
