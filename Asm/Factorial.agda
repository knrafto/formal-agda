{-# OPTIONS --cubical #-}
module Asm.Factorial where

open import Math.Bit
open import Math.Nat
open import Math.Type

-- A register. We use ℕ for simplicity.
Register : Type₀
Register = ℕ

r0 : Register
r0 = 0

r1 : Register
r1 = 1

¬r0≡r1 : ¬ r0 ≡ r1
¬r0≡r1 = ¬zero≡suc

¬r1≡r0 : ¬ r1 ≡ r0
¬r1≡r0 = ¬suc≡zero

-- A program address. For now, they address individual instructions, so the next
-- instruction after one at address a is at address a + 1.
Address : Type₀
Address = ℕ

-- TODO: come up with a better name for this, and define it.
byte : ℕ → Byte
byte = {!!}

-- TODO: name and define
lemma : ∀ {n} → n < 2 ^ 8 → byte n ≡ byte 0 → n ≡ 0
lemma = {!!}

-- An operation consists of an opcode and operands.
-- An operation is data, and can be encoded as a bitstring and stored in memory.
data Operation : Type₀ where
  nop  : Operation
  li   : Register → Byte → Operation
  bz   : Register → Address → Operation
  mul  : Register → Register → Register → Operation
  subi : Register → Register → Byte → Operation
  j    : Address → Operation

-- A program consists of a set of instructions, each with an operation and a unique address.
record Program : Type₁ where
  field
    Instruction : Type₀
    -- TODO: uniqueness
    address : Instruction → Address
    operation : Instruction → Operation

module Semantics (p : Program) where
  open Program p

  postulate
    -- An execution represents the event in which an instruction is processed.
    Execution : Type₀
    instruction : Execution → Instruction

    value : Execution → Register → Byte

  module li-props (e : Execution) (i i' : Instruction) (rd : Register) (v : Byte)
      (_ : instruction e ≡ i) (_ : operation i ≡ li rd v) (_ : address i' ≡ address i + 1) where
    postulate
      li-next : Execution
      li-next-instruction : instruction li-next ≡ i'
      li-rd : value li-next rd ≡ v
      li-other : ∀ r v → ¬ r ≡ rd → value e r ≡ v → value li-next r ≡ v

  module bz-props (e : Execution) (i taken not-taken : Instruction) (r : Register) (a : Address)
      (_ : instruction e ≡ i) (_ : operation i ≡ bz r a)
      (_ : address taken ≡ a) (_ : address not-taken ≡ address i + 1) where
    postulate
      bz-next : Execution
      bz-next-instruction-taken : value e r ≡ byte 0 → instruction bz-next ≡ taken
      bz-next-instruction-not-taken : ¬ (value e r ≡ byte 0) → instruction bz-next ≡ not-taken
      bz-other : ∀ r v → value e r ≡ v → value bz-next r ≡ v

  module mul-props (e : Execution) (i i' : Instruction) (rd rs rt : Register)
      (_ : instruction e ≡ i) (_ : operation i ≡ mul rd rs rt) (_ : address i' ≡ address i + 1) where
    postulate
      mul-next : Execution
      mul-next-instruction : instruction mul-next ≡ i'
      mul-rd : ∀ m n → value e rs ≡ byte m → value e rt ≡ byte n → value mul-next rd ≡ byte (m * n)
      mul-other : ∀ r v → ¬ r ≡ rd → value e r ≡ v → value mul-next r ≡ v

  module subi-props (e : Execution) (i i' : Instruction) (rd rs : Register) (v : Byte)
      (_ : instruction e ≡ i) (_ : operation i ≡ subi rd rs v) (_ : address i' ≡ address i + 1) where
    postulate
      subi-next : Execution
      subi-next-instruction : instruction subi-next ≡ i'
      subi-rd : ∀ m n k → byte k ≡ v → k + n ≡ m → value e rs ≡ byte m → value subi-next rd ≡ byte n
      subi-other : ∀ r v → ¬ r ≡ rd → value e r ≡ v → value subi-next r ≡ v

  module j-props (e : Execution) (i i' : Instruction) (a : Address)
      (_ : instruction e ≡ i) (_ : operation i ≡ j a)
      (_ : address i' ≡ a) where
    postulate
      j-next : Execution
      j-next-instruction : instruction j-next ≡ i'
      j-other : ∀ r v → value e r ≡ v → value j-next r ≡ v

module Factorial where
  data Instruction : Type₀ where
    start : Instruction
    loop₀ : Instruction
    loop₁ : Instruction
    loop₂ : Instruction
    loop₃ : Instruction
    done  : Instruction

  address : Instruction → Address
  address start = 0x00
  address loop₀ = 0x01
  address loop₁ = 0x02
  address loop₂ = 0x03
  address loop₃ = 0x04
  address done  = 0x05

  operation : Instruction → Operation
  operation start = li r1 (byte 1)
  operation loop₀ = bz r0 0x05  -- done
  operation loop₁ = mul r1 r1 r0
  operation loop₂ = subi r0 r0 (byte 1)
  operation loop₃ = j 0x01  -- loop₀
  operation done  = nop

  program : Program
  program = record { Instruction = Instruction; address = address; operation = operation }

  open Semantics program

  factorial : ℕ → ℕ
  factorial zero = 1
  factorial (suc n) = suc n * factorial n

  loop-property
    : (n : ℕ) → n < 2 ^ 8 → (r : ℕ) (e : Execution) → instruction e ≡ loop₀
    → value e r0 ≡ byte n
    → value e r1 ≡ byte r
    → Σ[ e' ∈ Execution ] (instruction e' ≡ done) × (value e' r1 ≡ byte (r * factorial n))
  loop-property zero _ r e e-loop₀ e-r0 e-r1 =
    let module e-props = bz-props e loop₀ done loop₁ r0 0x05 e-loop₀ refl refl refl
        e' = e-props.bz-next
        e'-done = e-props.bz-next-instruction-taken e-r0
        e'-r1 = e-props.bz-other r1 (byte r) e-r1
    in e' , e'-done , subst (λ n → value e' r1 ≡ byte n) (sym (*-1 r)) e'-r1
  loop-property (suc n) sucn<2^8 r e e-loop₀ e-r0 e-r1 =
    let module e-props = bz-props e loop₀ done loop₁ r0 0x05 e-loop₀ refl refl refl
 
        e₁ = e-props.bz-next
        e₁-loop₁ = e-props.bz-next-instruction-not-taken λ e-r0≡byte0 → ¬suc≡zero (lemma sucn<2^8 (sym e-r0 ∙ e-r0≡byte0))
        e₁-r0 = e-props.bz-other r0 (byte (suc n)) e-r0
        e₁-r1 = e-props.bz-other r1 (byte r) e-r1

        module e₁-props = mul-props e₁ loop₁ loop₂ r1 r1 r0 e₁-loop₁ refl refl

        e₂ = e₁-props.mul-next
        e₂-loop₂ = e₁-props.mul-next-instruction
        e₂-r0 = e₁-props.mul-other r0 (byte (suc n)) ¬r0≡r1 e₁-r0
        e₂-r1 = e₁-props.mul-rd r (suc n) e₁-r1 e₁-r0

        module e₂-props = subi-props e₂ loop₂ loop₃ r0 r0 (byte 1) e₂-loop₂ refl refl

        e₃ = e₂-props.subi-next
        e₃-loop₃ = e₂-props.subi-next-instruction
        e₃-r0 = e₂-props.subi-rd (suc n) n 1 refl refl e₂-r0
        e₃-r1 = e₂-props.subi-other r1 (byte (r * suc n)) ¬r1≡r0 e₂-r1

        module e₃-props = j-props e₃ loop₃ loop₀ 0x01 e₃-loop₃ refl refl

        e₄ = e₃-props.j-next
        e₄-loop₀ = e₃-props.j-next-instruction
        e₄-r0 = e₃-props.j-other r0 (byte n) e₃-r0
        e₄-r1 = e₃-props.j-other r1 (byte (r * suc n)) e₃-r1

        e' , e'-done , e'-r1 = loop-property n (<-trans ≤-refl sucn<2^8) (r * suc n) e₄ e₄-loop₀ e₄-r0 e₄-r1
    in e' , e'-done , subst (λ n → value e' r1 ≡ byte n) (sym (*-assoc r (suc n) (factorial n))) e'-r1

  program-property
    : (n : ℕ) → n < 2 ^ 8 → (e : Execution) → instruction e ≡ start → value e r0 ≡ byte n
    → Σ[ e' ∈ Execution ] (instruction e' ≡ done) × (value e' r1 ≡ byte (factorial n))
  program-property n n<2^8 e e-start e-r0 =
    let module e-props = li-props e start loop₀ r1 (byte 1) e-start refl refl
        e' = e-props.li-next
        e'-loop₀ = e-props.li-next-instruction
        e'-r0 = e-props.li-other r0 (byte n) ¬r0≡r1 e-r0
        e'-r1 = e-props.li-rd
        e'' , e''-done , e''-r1 = loop-property n n<2^8 1 e' e'-loop₀ e'-r0 e'-r1
    in e'' , e''-done , subst (λ n → value e'' r1 ≡ byte n) (1-* (factorial n)) e''-r1
