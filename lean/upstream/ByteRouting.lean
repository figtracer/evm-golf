import Bytes
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace GolfByteRouting

-- Bounds are part of the route, so routing never silently admits truncated bytes.
structure Route (whole : ByteArray) (base : Nat) (leaf : ByteArray) : Prop where
  bound : base + leaf.size ≤ whole.size
  fetch : ∀ i, i < leaf.size → whole.data[base+i]? = leaf.data[i]?

theorem left (a b : ByteArray) : Route (ByteArray.mk (a.data ++ b.data)) 0 a := by
  constructor
  · change 0 + a.data.size ≤ (a.data ++ b.data).size
    rw [Array.size_append]
    omega
  · intro i hi
    change (a.data ++ b.data)[0+i]? = a.data[i]?
    simpa only [Nat.zero_add] using (Array.getElem?_append_left hi)

theorem right (a b : ByteArray) : Route (ByteArray.mk (a.data ++ b.data)) a.size b := by
  constructor
  · change a.data.size + b.data.size ≤ (a.data ++ b.data).size
    rw [Array.size_append]
    omega
  · intro i hi
    change (a.data ++ b.data)[a.data.size+i]? = b.data[i]?
    rw [Array.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]

-- The parent and child bounds ensure every intermediate lookup is in range.
-- Named applications down a balanced tree retain logarithmic route depth.
theorem trans (whole middle leaf : ByteArray) (outer inner : Nat)
    (parent : Route whole outer middle) (child : Route middle inner leaf) :
    Route whole (outer+inner) leaf := by
  constructor
  · have hp := parent.bound
    have hc := child.bound
    omega
  · intro i hi
    have hc := child.bound
    have inside : inner+i < middle.size := by omega
    calc
      whole.data[(outer+inner)+i]? = whole.data[outer+(inner+i)]? := by rw [Nat.add_assoc]
      _ = middle.data[inner+i]? := parent.fetch (inner+i) inside
      _ = leaf.data[i]? := child.fetch i hi

-- Adjacent routed leaves can be joined without flattening the surrounding image.
-- This also routes an instruction's immediate when a physical image-node boundary
-- lies between its bytes. Both leaves must already be bound to the same full code.
theorem adjacent (whole a b : ByteArray) (base : Nat)
    (ha : Route whole base a) (hb : Route whole (base+a.size) b) :
    Route whole base (ByteArray.mk (a.data ++ b.data)) := by
  constructor
  · change base + (a.data ++ b.data).size ≤ whole.size
    rw [Array.size_append]
    have bound := hb.bound
    change base + a.data.size + b.data.size ≤ whole.data.size at bound
    change base + (a.data.size + b.data.size) ≤ whole.data.size
    omega
  · intro i hi
    change whole.data[base+i]? = (a.data ++ b.data)[i]?
    by_cases h : i < a.data.size
    · rw [Array.getElem?_append_left h]
      exact ha.fetch i h
    · have ge : a.data.size ≤ i := by omega
      rw [Array.getElem?_append_right ge]
      have len : i < a.data.size+b.data.size := by
        change i < (a.data ++ b.data).size at hi
        simpa only [Array.size_append] using hi
      have inB : i-a.size < b.size := by
        change i-a.data.size < b.data.size
        omega
      have fetched := hb.fetch (i-a.size) inB
      have offset : (base+a.size)+(i-a.size) = base+i := by
        change a.data.size ≤ i at ge
        change (base+a.data.size)+(i-a.data.size) = base+i
        omega
      rw [offset] at fetched
      exact fetched

#print axioms left
#print axioms right
#print axioms trans
#print axioms adjacent
end GolfByteRouting
