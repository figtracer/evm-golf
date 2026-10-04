import CheckedBoundaryMembership
import ByteRouting
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option autoImplicit false
open EvmYul EvmYul.EVM GolfLayout GolfByteRouting
namespace GolfRouteMembership

theorem byte_get (code : ByteArray) (i : Nat) : code.get? i = code.data[i]? := by
  simp only [ByteArray.get?, getElem?_def, ByteArray.size, ByteArray.get]

-- No image flattening: extensionality relates symbolic arrays at bounded indices.
theorem route_take (whole lead : ByteArray) (route : Route whole 0 lead) :
    whole.data.toList.take lead.size = lead.data.toList := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < lead.size
  · rw [List.getElem?_take_of_lt hi]
    simpa only [Array.getElem?_toList, Nat.zero_add] using route.fetch i hi
  · have leftNone : (whole.data.toList.take lead.size)[i]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      simp only [List.length_take]
      omega
    have rightNone : lead.data.toList[i]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      change lead.data.size ≤ i
      change ¬ i < lead.data.size at hi
      omega
    rw [leftNone, rightNone]

-- Obtaining the head from get? proves the boundary is strictly within the image.
theorem route_binding (whole lead : ByteArray) (route : Route whole 0 lead)
    (nextByte : whole.get? lead.size = some (UInt8.ofNat 91)) :
    whole.data.toList.map UInt8.toNat =
      lead.data.toList.map UInt8.toNat ++
        (91 :: ((whole.data.toList.drop (lead.size+1)).map UInt8.toNat)) := by
  have fetched : whole.data.toList[lead.size]? = some (UInt8.ofNat 91) := by
    rw [byte_get] at nextByte
    simpa only [Array.getElem?_toList] using nextByte
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp fetched
  have dropHead : whole.data.toList.drop lead.size =
      UInt8.ofNat 91 :: whole.data.toList.drop (lead.size+1) := by
    rw [List.drop_eq_getElem_cons inside, value]
  have partition := List.take_append_drop lead.size whole.data.toList
  rw [route_take whole lead route, dropHead] at partition
  have mapped := congrArg (List.map UInt8.toNat) partition
  simpa only [List.map_append, List.map_cons] using mapped.symm

-- Canonical code stays whole; only the prefix witness is routed into it.
-- No assumption about the suffix's scanner completeness or final PUSH is needed.
theorem contains_of_route (whole lead : ByteArray) (steps : Nat)
    (route : Route whole 0 lead)
    (complete : CompleteScanPrefix (lead.data.toList.map UInt8.toNat) steps)
    (nextByte : whole.get? lead.size = some (UInt8.ofNat 91))
    (bound : whole.size+32 < UInt256.size) :
    (D_J whole (UInt256.ofNat 0)).contains (UInt256.ofNat lead.size) = true := by
  exact GolfBoundaryMembership.contains_of_binding whole lead
    ((whole.data.toList.drop (lead.size+1)).map UInt8.toNat) steps complete
    (route_binding whole lead route nextByte) bound

end GolfRouteMembership

#print axioms GolfRouteMembership.byte_get
#print axioms GolfRouteMembership.route_take
#print axioms GolfRouteMembership.route_binding
#print axioms GolfRouteMembership.contains_of_route
