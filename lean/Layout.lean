/-!
Structural certificates for fixed-layout legacy bytecode rewrites. This checks
artifact derivation and local stack fragments, not whole-EVM execution or gas.
-/

namespace GolfLayout

structure Site where
  pc : Nat
  before : List Nat
  after : List Nat
  requiredStack : Nat
  deriving DecidableEq

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
    else if op = 128 then
      let next := height + 1
      profileAux fuel rest next (max required (1 - height).toNat) (max peak next.toNat)
    else if op = 80 then
      profileAux fuel rest (height - 1) (max required (1 - height).toNat) peak
    else none

def profile (code : List Nat) : Option (Nat × Int × Nat) :=
  profileAux (code.length + 1) code 0 0 0

def FragmentEquivalent (before after : List Nat) : Prop :=
  ∀ (a x y : Golf.Word) (tail : List Golf.Word),
    ∃ output, Golf.run (before.length + 1) before (a :: tail) x y = some output ∧
      Golf.run (after.length + 1) after (a :: tail) x y = some output

def LiteralEquivalent (before after : List Nat) : Prop :=
  ∀ (stack : List Golf.Word) (x y : Golf.Word),
    ∃ output, Golf.run (before.length + 1) before stack x y = some output ∧
      Golf.run (after.length + 1) after stack x y = some output

structure GrowthLiteralEquivalent (before after : List Nat) (growth : Nat) : Prop where
  positive : 0 < growth
  fits : growth ≤ 1024
  beforeProfile : profile before = some (0, (growth : Int), growth)
  afterProfile : profile after = some (0, (growth : Int), growth)
  equal : ∀ stack x y,
    GolfBounded.run (before.length + 1) before stack x y =
      GolfBounded.run (after.length + 1) after stack x y
  success : ∀ stack x y, stack.length + growth ≤ 1024 →
    ∃ output, GolfBounded.run (before.length + 1) before stack x y = some output ∧
      GolfBounded.run (after.length + 1) after stack x y = some output
  overflow : ∀ stack x y, 1024 < stack.length + growth →
    GolfBounded.run (before.length + 1) before stack x y = none ∧
      GolfBounded.run (after.length + 1) after stack x y = none

-- Shared exact shape gate: no caller-provided growth and no generic profile admission.
def zeroChainBytes (code : List Nat) : List Nat :=
  code.drop 1 |>.take (code.head! - 95)

def zeroChainTail (code : List Nat) : List Nat :=
  code.drop ((zeroChainBytes code).length + 1)

def zeroChainShape (site : Site) : Bool :=
  let bytes := zeroChainBytes site.before
  let ops := zeroChainTail site.before
  decide (bytes.length ≤ 32) &&
    (decide (∀ b ∈ bytes, b < 256) &&
      (decide (site.before = (95 + bytes.length) :: (bytes ++ ops)) &&
        (decide (site.after = (95 + bytes.length) :: (bytes ++ ops.map (fun _ => 95))) &&
          (decide (BitVec.ofNat 256 (Golf.immediate bytes) = 0) &&
            (decide (∀ op ∈ ops, op = 95 ∨ op = 128) &&
              (decide (ops.length ≤ 1023) && decide (128 ∈ ops)))))))

def zeroChainProfile (site : Site) : Bool :=
  let growth := (zeroChainTail site.before).length + 1
  zeroChainShape site &&
    (profile site.before == some (0, (growth : Int), growth) &&
      profile site.after == some (0, (growth : Int), growth))

inductive CertifiedSites : List Site → Prop where
  | nil : CertifiedSites []
  | cons {site : Site} {sites : List Site} :
      site.requiredStack = 1 → FragmentEquivalent site.before site.after →
      GolfBounded.FragmentEquivalent site.before site.after →
      GolfComposition.ContextEquivalent site.before site.after → CertifiedSites sites →
        CertifiedSites (site :: sites)
  | literalCons {site : Site} {sites : List Site} :
      site.requiredStack = 0 → LiteralEquivalent site.before site.after →
      GolfBounded.LiteralEquivalent site.before site.after →
      GolfComposition.ContextEquivalent site.before site.after → CertifiedSites sites →
        CertifiedSites (site :: sites)
  | chainCons {site : Site} {sites : List Site} {growth : Nat} :
      site.requiredStack = 0 → LiteralEquivalent site.before site.after →
      GrowthLiteralEquivalent site.before site.after growth →
      GolfComposition.ContextEquivalent site.before site.after → CertifiedSites sites →
        CertifiedSites (site :: sites)

structure LayoutArtifact (original candidate : List Nat) (sites : List Site) : Prop where
  originalBytes : original.all (fun byte => byte < 256) = true
  candidateBytes : candidate.all (fun byte => byte < 256) = true
  reconstructed : applySites original sites = some candidate
  sameLength : original.length = candidate.length
  sameLayout : scan original = scan candidate
  siteBoundaries : aligned sites ((scan original).map (fun item => item.1) ++ [original.length]) = true
  stackProfiles : sites.all (fun site =>
    if site.requiredStack == 1 then
      profile site.before == some (1, 0, 1) && profile site.after == some (1, 0, 1)
    else site.requiredStack == 0 &&
      ((profile site.before == some (0, 1, 2) && profile site.after == some (0, 1, 2)) ||
        (profile site.before == some (0, 2, 2) && profile site.after == some (0, 2, 2)) || zeroChainProfile site)) = true
  localProofs : CertifiedSites sites

-- These certificates describe literal byte reads, not memory execution, gas,
-- or control-flow equivalence. Both images are independently supplied above.
structure CodeCopy where
  pc : Nat
  prefixStart : Nat
  source : Nat
  length : Nat
  destination : Nat
  deriving DecidableEq

-- Decode a complete literal PUSH, including PUSH0, without EVM zero-padding.
def literalPush (code : List Nat) (pc : Nat) : Option (Nat × Nat) := do
  let op ← code[pc]?
  if 95 ≤ op ∧ op ≤ 127 ∧ pc + (op - 95) + 1 ≤ code.length then
    let value := ((code.drop (pc + 1)).take (op - 95)).foldl
      (fun value byte => value * 256 + byte) 0
    some (value, pc + (op - 95) + 1)
  else none

def copyPrefix (code : List Nat) (site : CodeCopy) : Bool :=
  match literalPush code site.prefixStart with
  | none => false
  | some (length, second) =>
    match literalPush code second with
    | none => false
    | some (source, third) =>
      match literalPush code third with
      | none => false
      | some (destination, finish) =>
        length == site.length && source == site.source &&
        destination == site.destination && finish == site.pc && code[finish]? == some 57

structure CodeCopyArtifact (original candidate : List Nat) (copies : List CodeCopy) : Prop where
  prefixes : copies.all (fun site =>
    ((scan original).map (fun item => item.1)).contains site.prefixStart &&
    ((scan candidate).map (fun item => item.1)).contains site.prefixStart &&
    copyPrefix original site && copyPrefix candidate site &&
    (original.drop site.prefixStart).take (site.pc + 1 - site.prefixStart) ==
      (candidate.drop site.prefixStart).take (site.pc + 1 - site.prefixStart)) = true
  sourceBounds : copies.all (fun site =>
    site.source + site.length ≤ original.length &&
    site.source + site.length ≤ candidate.length) = true
  copiedBytes : copies.all (fun site =>
    (original.drop site.source).take site.length ==
      (candidate.drop site.source).take site.length) = true

end GolfLayout
