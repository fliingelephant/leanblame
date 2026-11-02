import LeanBlame.Core.Sha256

/-! SHA-256 against FIPS 180-4's examples, and fed in pieces of every size from 1 to 130 bytes. -/

open LeanBlame

def expect (what got want : String) : IO Unit :=
  unless got == want do throw <| IO.userError s!"sha256, {what}: {got}, want {want}"

def main : IO Unit := do
  expect "empty" (Sha256.hexOfString "") "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  expect "abc" (Sha256.hexOfString "abc") "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  expect "two blocks" (Sha256.hexOfString "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  expect "a million a" (Sha256.hexOfString (String.ofList (List.replicate 1000000 'a')))
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
  let bytes := ByteArray.mk ((Array.range 1000).map (·.toUInt8))
  let whole := Sha256.hexOfBytes bytes
  for n in [1:131] do
    let mut s : Sha256.State := {}
    let mut off := 0
    while off < bytes.size do
      s := s.update (bytes.extract off (off + n))
      off := off + n
    expect s!"in pieces of {n} bytes" (Sha256.toHex s.finish) whole
