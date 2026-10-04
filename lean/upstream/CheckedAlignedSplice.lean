import CheckedCompleteSegments
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace GolfAlignedSplice
open GolfLayout GolfWindowArtifact

theorem targets_append (a b : List Row) :
    jumpTargets (a ++ b) = jumpTargets a ++ jumpTargets b := by
  simp only [jumpTargets, List.filter_append, List.map_append]

-- Source and candidate may consume different numbers of scanner steps.
-- The arbitrary suffix does not need CompleteScanPrefix: a final PUSH can truncate.
theorem scan_two (lead segment suffix : List Nat) (leadSteps segmentSteps : Nat)
    (leadComplete : CompleteScanPrefix lead leadSteps)
    (segmentComplete : CompleteScanPrefix segment segmentSteps) :
    scan (lead ++ segment ++ suffix) =
      scanAux leadSteps 0 lead ++
      scanAux segmentSteps lead.length segment ++
      scanAux suffix.length (lead.length + segment.length) suffix := by
  let p : CompleteChunk := ⟨lead, leadSteps, leadComplete⟩
  let a : CompleteChunk := ⟨segment, segmentSteps, segmentComplete⟩
  have h := scan_complete_chunks [p,a] suffix
  simpa only [p, a, chunkBytes, chunkRows, List.append_nil, List.length_append,
    Nat.zero_add, Nat.add_zero, List.append_assoc] using h

-- Equal target lists are sufficient; full instruction rows need not be equal.
-- Premise completeness is what prevents either segment from stealing PUSH bytes
-- from the adjacent lead/suffix. Equal length preserves absolute suffix PCs.
theorem targets_splice (lead before after suffix : List Nat)
    (leadSteps beforeSteps afterSteps : Nat)
    (leadComplete : CompleteScanPrefix lead leadSteps)
    (beforeComplete : CompleteScanPrefix before beforeSteps)
    (afterComplete : CompleteScanPrefix after afterSteps)
    (sameLength : before.length = after.length)
    (sameTargets : jumpTargets (scanAux beforeSteps lead.length before) =
      jumpTargets (scanAux afterSteps lead.length after)) :
    jumpTargets (scan (lead ++ before ++ suffix)) =
      jumpTargets (scan (lead ++ after ++ suffix)) := by
  rw [scan_two lead before suffix leadSteps beforeSteps leadComplete beforeComplete,
      scan_two lead after suffix leadSteps afterSteps leadComplete afterComplete]
  simp only [targets_append]
  rw [sameTargets, sameLength]

-- Specialization useful for masks: each side has zero scanned JUMPDESTs.
theorem targets_splice_empty (lead before after suffix : List Nat)
    (leadSteps beforeSteps afterSteps : Nat)
    (leadComplete : CompleteScanPrefix lead leadSteps)
    (beforeComplete : CompleteScanPrefix before beforeSteps)
    (afterComplete : CompleteScanPrefix after afterSteps)
    (sameLength : before.length = after.length)
    (beforeTargets : jumpTargets (scanAux beforeSteps lead.length before) = [])
    (afterTargets : jumpTargets (scanAux afterSteps lead.length after) = []) :
    jumpTargets (scan (lead ++ before ++ suffix)) =
      jumpTargets (scan (lead ++ after ++ suffix)) := by
  apply targets_splice lead before after suffix leadSteps beforeSteps afterSteps
    leadComplete beforeComplete afterComplete sameLength
  rw [beforeTargets, afterTargets]

end GolfAlignedSplice

#print axioms GolfAlignedSplice.targets_append
#print axioms GolfAlignedSplice.scan_two
#print axioms GolfAlignedSplice.targets_splice
#print axioms GolfAlignedSplice.targets_splice_empty
