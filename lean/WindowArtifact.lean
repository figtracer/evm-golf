/-! Exact mask-window certificates. The existing LayoutArtifact and checker
remain unchanged; only exact proved mask shapes may change interior boundaries. -/
namespace GolfWindowArtifact
open GolfLayout
def profileAuxExtended : Nat → List Nat → Int → Nat → Nat → Option (Nat × Int × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, [], height, required, peak => some (required, height, peak)
  | fuel + 1, op :: rest, height, required, peak =>
    if 95 ≤ op ∧ op ≤ 127 then
      let immediate := op - 95
      if immediate ≤ rest.length then
        let next := height + 1
        profileAuxExtended fuel (rest.drop immediate) next required (max peak next.toNat)
      else none
    else if op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 22 ∨ op = 27 then
      profileAuxExtended fuel rest (height - 1) (max required (2 - height).toNat) peak
    else if op = 25 then
      profileAuxExtended fuel rest height (max required (1 - height).toNat) peak
    else if op = 128 then
      let next := height + 1
      profileAuxExtended fuel rest next (max required (1 - height).toNat) (max peak next.toNat)
    else if 129 ≤ op ∧ op ≤ 143 then
      let next := height + 1
      profileAuxExtended fuel rest next (max required (((op - 127 : Nat) : Int) - height).toNat) (max peak next.toNat)
    else if 144 ≤ op ∧ op ≤ 159 then
      profileAuxExtended fuel rest height (max required (((op - 142 : Nat) : Int) - height).toNat) peak
    else if op = 80 then
      profileAuxExtended fuel rest (height - 1) (max required (1 - height).toNat) peak
    else none

def profileExtended (code : List Nat) : Option (Nat × Int × Nat) :=
  profileAuxExtended (code.length + 1) code 0 0 0



def maskShape (site : Site) : Bool :=
 site.requiredStack == 1 && site.before == GolfMaskWindow.before && site.after == GolfMaskWindow.after

structure MaskEquivalent (site : Site) : Prop where
 shape : maskShape site = true
 beforeProfile : profileExtended site.before = some (1,1,3)
 afterProfile : profileExtended site.after = some (1,1,3)
 equal : ∀ stack x y, GolfBounded.run (site.before.length+1) site.before stack x y =
   GolfBounded.run (site.after.length+1) site.after stack x y
 output : ∀ a tail x y,
   Golf.run (site.before.length+1) site.before (a::tail) x y = some (GolfMaskWindow.output a tail) ∧
   Golf.run (site.after.length+1) site.after (a::tail) x y = some (GolfMaskWindow.output a tail)
 success : ∀ a tail x y, tail.length ≤ 1020 →
   GolfBounded.run (site.before.length+1) site.before (a::tail) x y = some (GolfMaskWindow.output a tail) ∧
   GolfBounded.run (site.after.length+1) site.after (a::tail) x y = some (GolfMaskWindow.output a tail)
 underflow : ∀ x y, GolfBounded.run (site.before.length+1) site.before [] x y = none ∧
   GolfBounded.run (site.after.length+1) site.after [] x y = none
 overflow : ∀ stack x y, 1022 ≤ stack.length →
   GolfBounded.run (site.before.length+1) site.before stack x y = none ∧
   GolfBounded.run (site.after.length+1) site.after stack x y = none
 context : GolfComposition.ContextEquivalent site.before site.after

theorem exact_mask (pc : Nat) : MaskEquivalent ⟨pc,GolfMaskWindow.before,GolfMaskWindow.after,1⟩ := by
 refine ⟨by rfl, by change profileExtended GolfMaskWindow.before = some (1,1,3); decide +kernel, by change profileExtended GolfMaskWindow.after = some (1,1,3); decide +kernel, ?_, ?_, ?_, ?_, ?_, GolfMaskWindow.context⟩
 · exact GolfMaskWindow.bounded
 · intro a tail x y; exact ⟨GolfMaskWindow.before_output a x y tail, GolfMaskWindow.after_output a x y tail⟩
 · intro a tail x y h; exact GolfMaskWindow.success a x y tail h
 · exact GolfMaskWindow.underflow
 · exact GolfMaskWindow.overflow

def idempotentShape (site : Site) : Bool :=
 site.requiredStack == 1 && site.before == GolfIdempotentMask.before && site.after == GolfIdempotentMask.after

structure IdempotentEquivalent (site : Site) : Prop where
 shape : idempotentShape site = true
 beforeProfile : profileExtended site.before = some (1,0,3)
 afterProfile : profileExtended site.after = some (1,0,3)
 equal : ∀ stack x y, GolfBounded.run (site.before.length+1) site.before stack x y =
   GolfBounded.run (site.after.length+1) site.after stack x y
 output : ∀ a tail x y,
   Golf.run (site.before.length+1) site.before (a::tail) x y = some (GolfIdempotentMask.output a tail) ∧
   Golf.run (site.after.length+1) site.after (a::tail) x y = some (GolfIdempotentMask.output a tail)
 success : ∀ a tail x y, tail.length ≤ 1020 →
   GolfBounded.run (site.before.length+1) site.before (a::tail) x y = some (GolfIdempotentMask.output a tail) ∧
   GolfBounded.run (site.after.length+1) site.after (a::tail) x y = some (GolfIdempotentMask.output a tail)
 underflow : ∀ x y, GolfBounded.run (site.before.length+1) site.before [] x y = none ∧
   GolfBounded.run (site.after.length+1) site.after [] x y = none
 overflow : ∀ stack x y, 1022 ≤ stack.length →
   GolfBounded.run (site.before.length+1) site.before stack x y = none ∧
   GolfBounded.run (site.after.length+1) site.after stack x y = none
 context : GolfComposition.ContextEquivalent site.before site.after

theorem exact_idempotent (pc : Nat) : IdempotentEquivalent ⟨pc,GolfIdempotentMask.before,GolfIdempotentMask.after,1⟩ := by
 refine ⟨by rfl, by change profileExtended GolfIdempotentMask.before = some (1,0,3); decide +kernel, by change profileExtended GolfIdempotentMask.after = some (1,0,3); decide +kernel, ?_, ?_, ?_, ?_, ?_, GolfIdempotentMask.context⟩
 · exact GolfIdempotentMask.bounded
 · intro a tail x y; exact ⟨GolfIdempotentMask.before_output a x y tail, GolfIdempotentMask.after_output a x y tail⟩
 · intro a tail x y h; exact GolfIdempotentMask.success a x y tail h
 · exact GolfIdempotentMask.underflow
 · exact GolfIdempotentMask.overflow

def reuseShape (site : Site) : Bool :=
 (site.requiredStack == 2 && site.before == GolfMaskReuse.before2 && site.after == GolfMaskReuse.after2) ||
 (site.requiredStack == 7 && site.before == GolfMaskReuse.before7 && site.after == GolfMaskReuse.after7)

structure ReuseEquivalent (site : Site) : Prop where
 shape : reuseShape site = true
 beforeProfile : profileExtended site.before = some (site.requiredStack,1,4)
 afterProfile : profileExtended site.after = some (site.requiredStack,1,4)
 equal : ∀ stack x y, GolfBounded.run (site.before.length+1) site.before stack x y =
   GolfBounded.run (site.after.length+1) site.after stack x y
 success : ∀ stack x y, site.requiredStack ≤ stack.length → stack.length ≤ 1020 →
   ∃ output, GolfBounded.run (site.before.length+1) site.before stack x y = some output ∧
     GolfBounded.run (site.after.length+1) site.after stack x y = some output
 underflow : ∀ stack x y, stack.length < site.requiredStack →
   GolfBounded.run (site.before.length+1) site.before stack x y = none ∧
   GolfBounded.run (site.after.length+1) site.after stack x y = none
 overflow : ∀ stack x y, 1021 ≤ stack.length →
   GolfBounded.run (site.before.length+1) site.before stack x y = none ∧
   GolfBounded.run (site.after.length+1) site.after stack x y = none
 context : GolfComposition.ContextEquivalent site.before site.after

theorem exact_reuse2 (pc : Nat) : ReuseEquivalent ⟨pc,GolfMaskReuse.before2,GolfMaskReuse.after2,2⟩ := by
 refine ⟨by rfl, ?_, ?_, GolfMaskReuse.all_height2, GolfMaskReuse.success2,
   GolfMaskReuse.underflow2, GolfMaskReuse.overflow2, GolfMaskReuse.context2⟩
 · change profileExtended GolfMaskReuse.before2 = some (2,1,4)
   decide +kernel
 · change profileExtended GolfMaskReuse.after2 = some (2,1,4)
   decide +kernel

theorem exact_reuse7 (pc : Nat) : ReuseEquivalent ⟨pc,GolfMaskReuse.before7,GolfMaskReuse.after7,7⟩ := by
 refine ⟨by rfl, ?_, ?_, GolfMaskReuse.all_height7, GolfMaskReuse.success7,
   GolfMaskReuse.underflow7, GolfMaskReuse.overflow7, GolfMaskReuse.context7⟩
 · change profileExtended GolfMaskReuse.before7 = some (7,1,4)
   decide +kernel
 · change profileExtended GolfMaskReuse.after7 = some (7,1,4)
   decide +kernel

def windowShape (site : Site) : Bool := maskShape site || idempotentShape site || reuseShape site

-- Existing sites must retain all their original structural and local obligations.
inductive CertifiedWindowSites : List Site → Prop where
 | nil : CertifiedWindowSites []
 | old {site : Site} {sites : List Site} :
     LayoutArtifact site.before site.after [⟨0,site.before,site.after,site.requiredStack⟩] →
     CertifiedWindowSites sites → CertifiedWindowSites (site::sites)
 | mask {site : Site} {sites : List Site} :
     MaskEquivalent site → CertifiedWindowSites sites → CertifiedWindowSites (site::sites)
 | idempotent {site : Site} {sites : List Site} :
     IdempotentEquivalent site → CertifiedWindowSites sites → CertifiedWindowSites (site::sites)
 | reuse {site : Site} {sites : List Site} :
     ReuseEquivalent site → CertifiedWindowSites sites → CertifiedWindowSites (site::sites)

def interior (site : Site) (pc : Nat) : Bool := site.pc < pc && pc < site.pc+site.before.length
def inMask (sites : List Site) (pc : Nat) : Bool :=
 sites.any (fun site => windowShape site && site.pc ≤ pc && pc < site.pc+site.before.length)
def exterior (sites : List Site) (rows : List Row) := rows.filter (fun row => !inMask sites row.1)
def noInteriorJump (sites : List Site) (rows : List Row) : Bool :=
 rows.all (fun row => !row.2.2 || sites.all (fun site => !windowShape site || !interior site row.1))
def disjoint (start size otherStart otherSize : Nat) : Bool :=
 size == 0 || otherSize == 0 || start+size ≤ otherStart || otherStart+otherSize ≤ start

def protectedCopies (sites : List Site) (copies : List CodeCopy) : Bool :=
 sites.all (fun site => copies.all (fun copy =>
   disjoint site.pc site.before.length copy.source copy.length &&
   disjoint site.pc site.before.length copy.prefixStart (copy.pc+1-copy.prefixStart)))

structure WindowArtifact (original candidate : List Nat) (sites : List Site)
 (copies : List CodeCopy) : Prop where
 originalBytes : original.all (fun b => b<256) = true
 candidateBytes : candidate.all (fun b => b<256) = true
 reconstructed : applySites original sites = some candidate
 sameLength : original.length = candidate.length
 sourceBoundaries : aligned sites ((scan original).map (fun row => row.1) ++ [original.length]) = true
 targetBoundaries : aligned sites ((scan candidate).map (fun row => row.1) ++ [candidate.length]) = true
 exteriorEqual : exterior sites (scan original) = exterior sites (scan candidate)
 jumpTargetsEqual : jumpTargets (scan original) = jumpTargets (scan candidate)
 sourceInterior : noInteriorJump sites (scan original) = true
 targetInterior : noInteriorJump sites (scan candidate) = true
 certificates : CertifiedWindowSites sites
 copiesValid : CodeCopyArtifact original candidate copies
 copiesProtected : protectedCopies sites copies = true

-- Copy enumeration remains trusted gate analysis, exactly as in existing product.
-- This proposition does not assert that the supplied list covers all possible code reads.
end GolfWindowArtifact
