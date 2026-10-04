import EvmYul.EVM.Semantics
import LayoutScanner
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfParserFacts

def Agrees (byte : UInt8) : Prop :=
  let op := (parseInstr byte).getD .INVALID
  parseInstr byte = some op ∧
  argOnNBytesOfInstr op = (if 96 ≤ byte.toNat ∧ byte.toNat ≤ 127 then byte.toNat - 95 else 0) ∧
  (op = .JUMPDEST ↔ byte.toNat = 91)

instance (byte : UInt8) : Decidable (Agrees byte) := by unfold Agrees; infer_instance

theorem parser_table : ∀ n : Fin 256, Agrees (UInt8.ofNat n.val) := by decide

theorem parser_agrees (byte : UInt8) : Agrees byte := by
  have fact := parser_table ⟨byte.toNat, byte.toNat_lt_size⟩
  simpa only [UInt8.ofNat_toNat] using fact

theorem parser_present (byte : UInt8) :
    parseInstr byte = some ((parseInstr byte).getD .INVALID) := (parser_agrees byte).1

theorem parser_width (byte : UInt8) :
    argOnNBytesOfInstr ((parseInstr byte).getD .INVALID) =
      (if 96 ≤ byte.toNat ∧ byte.toNat ≤ 127 then byte.toNat - 95 else 0) :=
  (parser_agrees byte).2.1

theorem parser_jumpdest (byte : UInt8) :
    ((parseInstr byte).getD .INVALID = .JUMPDEST ↔ byte.toNat = 91) :=
  (parser_agrees byte).2.2

end GolfParserFacts

#print axioms GolfParserFacts.parser_table
#print axioms GolfParserFacts.parser_agrees
#print axioms GolfParserFacts.parser_present
#print axioms GolfParserFacts.parser_width
#print axioms GolfParserFacts.parser_jumpdest
