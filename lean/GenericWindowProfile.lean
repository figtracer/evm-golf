/- Proposal-only decoding and stack metadata. Legacy GolfLayout.profile is unchanged. -/
namespace GolfGenericWindow

def supportedAux : Nat → List Nat → Bool
 | 0, _ => false
 | _+1, [] => true
 | fuel+1, op::rest =>
   if 95 ≤ op ∧ op ≤ 127 then
     let width := op-95
     width ≤ rest.length && supportedAux fuel (rest.drop width)
   else (op == 1 || op == 3 || op == 22 || op == 23 || op == 24 || op == 25 || op == 27 || op == 80 ||
     (128 ≤ op && op ≤ 159)) && supportedAux fuel rest

def supported (code : List Nat) : Bool := supportedAux (code.length+1) code

-- Binary operations consume two words; NOT replaces one word.
-- DUP requires its decoded depth and adds one word without consuming inputs.
-- Like the legacy profiler, peak starts at0 and includes transient growth.
def profileAux : Nat → List Nat → Int → Nat → Nat → Option (Nat × Int × Nat)
 | 0, _, _, _, _ => none
 | _+1, [], height, required, peak => some (required,height,peak)
 | fuel+1, op::rest, height, required, peak =>
   if 95 ≤ op ∧ op ≤ 127 then
     let width := op-95
     if width ≤ rest.length then
       let next := height+1
       profileAux fuel (rest.drop width) next required (max peak next.toNat)
     else none
   else if op = 1 ∨ op = 3 ∨ op = 22 ∨ op = 23 ∨ op = 24 ∨ op = 27 then
     profileAux fuel rest (height-1) (max required (2-height).toNat) peak
   else if op = 80 then
     profileAux fuel rest (height-1) (max required (1-height).toNat) peak
   else if op = 25 then
     profileAux fuel rest height (max required (1-height).toNat) peak
   else if 128 ≤ op ∧ op ≤ 143 then
     let next := height+1
     profileAux fuel rest next (max required (Int.ofNat (op-127)-height).toNat)
       (max peak next.toNat)
   else if 144 ≤ op ∧ op ≤ 159 then
     profileAux fuel rest height (max required (Int.ofNat (op-142)-height).toNat) peak
   else none

def profile (code : List Nat) : Option (Nat × Int × Nat) :=
 profileAux (code.length+1) code 0 0 0

-- Grammar membership concerns decoded opcodes, not PUSH data byte values.
inductive LegacyPure : List Nat → Prop where
 | nil : LegacyPure []
 | push {op : Nat} {immediate rest : List Nat}
     (range : 95 ≤ op ∧ op ≤ 127)
     (width : immediate.length = op-95)
     (tail : LegacyPure rest) : LegacyPure (op::(immediate++rest))
 | andOp {rest : List Nat} (tail : LegacyPure rest) : LegacyPure (22::rest)
 | pop {rest : List Nat} (tail : LegacyPure rest) : LegacyPure (80::rest)

-- Same metadata on every old admitted pure fragment, arbitrary fuel and states.
theorem profileAux_legacy {code : List Nat} (grammar : LegacyPure code)
 (fuel : Nat) (height : Int) (required peak : Nat) :
 profileAux fuel code height required peak =
 GolfLayout.profileAux fuel code height required peak := by
 induction grammar generalizing fuel height required peak with
 | nil => cases fuel <;> rfl
 | @push op immediate rest range width tail ih =>
   cases fuel with
   | zero => rfl
   | succ fuel =>
     have enough : op-95 ≤ (immediate++rest).length := by simp only [List.length_append]; omega
     have drop : (immediate++rest).drop (op-95) = rest := by
       rw [←width]
       simp
     simp only [profileAux,GolfLayout.profileAux,range,if_pos,enough,drop]
     exact ih _ _ _ _
 | @andOp rest tail ih =>
   cases fuel with
   | zero => rfl
   | succ fuel =>
     change profileAux fuel rest (height-1) (max required (2-height).toNat) peak = _
     change _ = GolfLayout.profileAux fuel rest (height-1) (max required (2-height).toNat) peak
     exact ih _ _ _ _
 | @pop rest tail ih =>
   cases fuel with
   | zero => rfl
   | succ fuel =>
     change profileAux fuel rest (height-1) (max required (1-height).toNat) peak = _
     change _ = GolfLayout.profileAux fuel rest (height-1) (max required (1-height).toNat) peak
     exact ih _ _ _ _

theorem profile_legacy {code : List Nat} (grammar : LegacyPure code) :
 profile code = GolfLayout.profile code := profileAux_legacy grammar _ _ _ _

-- PUSH payload containing new opcode values does not alter legacy classification.
example : LegacyPure [97,3,27,80] :=
 .push (op := 97) (immediate := [3,27]) (rest := [80]) (by decide) (by decide) (.pop .nil)
end GolfGenericWindow
