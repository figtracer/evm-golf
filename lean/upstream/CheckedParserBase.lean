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

end GolfParserFacts
