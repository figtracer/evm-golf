import ByteRouting
import CheckedAlignedSplice
import CheckedTableEquality
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM GolfLayout GolfWindowArtifact
namespace SpliceSupport

theorem complete_append {a b : List Nat} {na nb : Nat}
 (ha : CompleteScanPrefix a na) (hb : CompleteScanPrefix b nb) :
 CompleteScanPrefix (a++b) (na+nb) := by
 induction ha with
 | nil => simpa using hb
 | cons op immediate rest steps width tail ih =>
   simpa only [List.cons_append,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
    CompleteScanPrefix.cons op immediate (rest++b) (steps+nb) width ih

theorem complete_bytes_append (a b : ByteArray) (na nb : Nat)
 (ha : CompleteScanPrefix (a.data.toList.map UInt8.toNat) na)
 (hb : CompleteScanPrefix (b.data.toList.map UInt8.toNat) nb) :
 CompleteScanPrefix ((ByteArray.mk (a.data++b.data)).data.toList.map UInt8.toNat) (na+nb) := by
 simpa only [Array.toList_append,List.map_append] using complete_append ha hb

theorem append_size (a b : ByteArray) (na nb : Nat) (ha : a.size=na) (hb : b.size=nb) :
 (ByteArray.mk (a.data++b.data)).size=na+nb := by
 change (a.data++b.data).size = _
 rw [Array.size_append]
 change a.size+b.size = _
 rw [ha,hb]

end SpliceSupport

namespace GolfJumpRoute
 theorem empty_route (whole : ByteArray) : GolfByteRouting.Route whole 0 (ByteArray.mk #[]) := by
  constructor
  · simp only [ByteArray.size, Array.size_empty, Nat.add_zero, Nat.zero_le]
  · intro i hi
    simp only [ByteArray.size, Array.size_empty, Nat.not_lt_zero] at hi
end GolfJumpRoute
#print axioms SpliceSupport.complete_append
#print axioms SpliceSupport.complete_bytes_append
#print axioms SpliceSupport.append_size
#print axioms GolfJumpRoute.empty_route
