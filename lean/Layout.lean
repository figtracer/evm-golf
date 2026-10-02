/-!
Structural certificates for fixed-layout legacy bytecode rewrites. This checks
artifact derivation and local stack fragments, not whole-EVM execution or gas.
-/

namespace GolfLayout

structure Site where
  pc : Nat
  before : List Nat
  after : List Nat
  deriving DecidableEq

-- PUSH data is skipped even when its final immediate is truncated. The scanner
-- describes the entire artifact, including unreachable bytes and metadata.
def scanAux : Nat → Nat → List Nat → List (Nat × Nat × Bool)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, pc, op :: rest =>
    let immediate := if 96 ≤ op ∧ op ≤ 127 then op - 95 else 0
    (pc, immediate + 1, op == 91) ::
      scanAux fuel (pc + immediate + 1) (rest.drop immediate)

def scan (code : List Nat) : List (Nat × Nat × Bool) :=
  scanAux (code.length + 1) 0 code

-- Reconstruct the candidate from exact original slices, retaining every byte
-- outside the sites. Traversal rejects overlap, reordering, empty replacements,
-- changed lengths, mismatched original slices, and out-of-range sites.
def applyFrom : Nat → List Nat → List Site → Option (List Nat)
  | _, code, [] => some code
  | cursor, code, site :: sites =>
    if site.pc < cursor ∨ site.before.isEmpty ∨ site.before.length ≠ site.after.length then none
    else
      let gap := site.pc - cursor
      if (code.drop gap).take site.before.length != site.before then none
      else
        match applyFrom (site.pc + site.before.length)
            (code.drop (gap + site.before.length)) sites with
        | none => none
        | some suffix => some (code.take gap ++ site.after ++ suffix)

def applySites (original : List Nat) (sites : List Site) : Option (List Nat) :=
  applyFrom 0 original sites

-- A merge walk over ordered boundaries avoids searching the whole artifact
-- again for every replacement. Both endpoints must be real instruction edges.
def aligned : List Site → List Nat → Bool
  | [], _ => true
  | site :: sites, boundaries =>
    let start := boundaries.dropWhile (fun pc => pc < site.pc)
    let finish := start.dropWhile (fun pc => pc < site.pc + site.before.length)
    start.head? == some site.pc &&
      finish.head? == some (site.pc + site.before.length) && aligned sites finish

-- Only the fragment instruction subset is profiled. A failed profile never
-- establishes equality by matching another failure. Gas is deliberately absent.
def profileAux : Nat → List Nat → Int → Nat → Nat → Option (Nat × Int × Nat)
  | 0, _, _, _, _ => none
  | _ + 1, [], height, required, peak => some (required, height, peak)
  | fuel + 1, op :: rest, height, required, peak =>
    if 95 ≤ op ∧ op ≤ 127 then
      let immediate := op - 95
      if immediate ≤ rest.length then
        let next := height + 1
        profileAux fuel (rest.drop immediate) next required (max peak next.toNat)
      else none
    else if op = 1 ∨ op = 2 ∨ op = 22 ∨ op = 27 then
      profileAux fuel rest (height - 1) (max required (2 - height).toNat) peak
    else none

def profile (code : List Nat) : Option (Nat × Int × Nat) :=
  profileAux (code.length + 1) code 0 0 0

def FragmentEquivalent (before after : List Nat) : Prop :=
  ∀ (a x y : Golf.Word) (tail : List Golf.Word),
    ∃ output, Golf.run (before.length + 1) before (a :: tail) x y = some output ∧
      Golf.run (after.length + 1) after (a :: tail) x y = some output

inductive CertifiedSites : List Site → Prop where
  | nil : CertifiedSites []
  | cons {site : Site} {sites : List Site} :
      FragmentEquivalent site.before site.after → CertifiedSites sites →
        CertifiedSites (site :: sites)

structure LayoutArtifact (original candidate : List Nat) (sites : List Site) : Prop where
  originalBytes : original.all (fun byte => byte < 256) = true
  candidateBytes : candidate.all (fun byte => byte < 256) = true
  reconstructed : applySites original sites = some candidate
  sameLength : original.length = candidate.length
  sameLayout : scan original = scan candidate
  siteBoundaries : aligned sites ((scan original).map (fun item => item.1) ++ [original.length]) = true
  stackProfiles : sites.all (fun site =>
    profile site.before == some (1, 0, 1) && profile site.after == some (1, 0, 1)) = true
  localProofs : CertifiedSites sites

end GolfLayout
