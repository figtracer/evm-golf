import CheckedParserBase
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace GolfParserFacts

-- Each bounded table is checked in its own module under the normal proof budget.
theorem parser_table2 : ∀ n : Fin 64, Agrees (UInt8.ofNat (128 + n.val)) := by decide

end GolfParserFacts
#print axioms GolfParserFacts.parser_table2
