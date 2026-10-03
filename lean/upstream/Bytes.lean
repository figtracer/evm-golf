import Std
set_option Elab.async false
namespace GolfArtifactBytes

/-- Interpret an artifact's natural-number bytes using Lean's canonical byte representation. -/
def encode (xs : List Nat) : ByteArray := ⟨(xs.map UInt8.ofNat).toArray⟩

/-- Recover natural-number bytes from the canonical array field, without a parallel decoder. -/
def bytes (code : ByteArray) : List Nat := code.data.toList.map UInt8.toNat

/-- The range obligation matters: UInt8.ofNat otherwise truncates modulo 256. -/
theorem bytes_encode (xs : List Nat) (valid : ∀ x ∈ xs, x < 256) :
    bytes (encode xs) = xs := by
  simp only [bytes, encode, List.toList_toArray, List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · exact UInt8.toNat_ofNat_of_lt' (valid x (by simp))
    · exact ih (fun y hy => valid y (by simp [hy]))

theorem range_of_all (xs : List Nat)
    (checked : xs.all (fun x => x < 256) = true) : ∀ x ∈ xs, x < 256 := by
  simpa using List.all_eq_true.mp checked

/-- Within the artifact byte range, conversion cannot silently identify different images. -/
theorem encode_injective (xs ys : List Nat)
    (vx : ∀ x ∈ xs, x < 256) (vy : ∀ y ∈ ys, y < 256)
    (same : encode xs = encode ys) : xs = ys := by
  have recovered := congrArg bytes same
  simpa only [bytes_encode xs vx, bytes_encode ys vy] using recovered

#print axioms bytes_encode
#print axioms encode_injective
end GolfArtifactBytes
