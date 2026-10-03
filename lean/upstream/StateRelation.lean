import Driver

/-! Canonical EVM region proof support against the pinned upstream semantics. -/
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfUpstream

def AccountsRelated (owner address : AccountAddress) (old new : ByteArray)
    (a b : Account .EVM) : Prop :=
  a.nonce = b.nonce ∧ a.balance = b.balance ∧ a.storage = b.storage ∧
  a.tstorage = b.tstorage ∧
  (if address = owner then a.code = old ∧ b.code = new else a.code = b.code)

def MapsRelated (owner : AccountAddress) (old new : ByteArray)
    (a b : AccountMap .EVM) : Prop :=
  ∀ address, match a.find? address, b.find? address with
  | none, none => True
  | some x, some y => AccountsRelated owner address old new x y
  | _, _ => False

def Linked (owner : AccountAddress) (code : ByteArray) (s : EVM.State) : Prop :=
  s.executionEnv.codeOwner = owner ∧ s.executionEnv.code = code ∧
  (∃ a, s.accountMap.find? owner = some a ∧ a.code = code) ∧
  (∃ a, s.σ₀.find? owner = some a ∧ a.code = code)

def DeployedMaps (owner : AccountAddress) (old new : ByteArray)
    (s t : EVM.State) : Prop :=
  MapsRelated owner old new s.accountMap t.accountMap ∧
  MapsRelated owner old new s.σ₀ t.σ₀ ∧ Linked owner old s ∧ Linked owner new t

def eraseMaps (s : EVM.State) : EVM.State :=
  { s with accountMap := default, σ₀ := default }

def deployedFrame (s : EVM.State) : EVM.State := eraseMaps (eraseCodeGas s)

theorem frame_code (s t : EVM.State) (old new : ByteArray)
    (h : deployedFrame s = deployedFrame t) :
    deployedFrame (withCode s old) = deployedFrame (withCode t new) := h

theorem frame_push_deployed (s t : EVM.State) (v : UInt256) (w : Nat)
    (h : deployedFrame s = deployedFrame t) :
    deployedFrame (pushedWidth s v w) = deployedFrame (pushedWidth t v w) := by
  have hh := congrArg (fun x => pushedWidth x v w) h
  simpa only [deployedFrame, eraseMaps, eraseCodeGas, pushedWidth] using
    congrArg deployedFrame hh

theorem frame_binary_deployed (s t : EVM.State) (v : UInt256) (tail : List UInt256) (cost : Nat)
    (h : deployedFrame s = deployedFrame t) :
    deployedFrame (binaryPost s v tail cost) = deployedFrame (binaryPost t v tail cost) := by
  have hh := congrArg (fun x => binaryPost x v tail cost) h
  simpa only [deployedFrame, eraseMaps, eraseCodeGas, binaryPost] using
    congrArg deployedFrame hh

theorem frame_stop_deployed (s t : EVM.State)
    (h : deployedFrame s = deployedFrame t) :
    deployedFrame (stopped s) = deployedFrame (stopped t) := by
  have hh := congrArg stopped h
  simpa only [deployedFrame, eraseMaps, eraseCodeGas, stopped] using hh


#print axioms frame_push_deployed
#print axioms frame_binary_deployed
#print axioms frame_stop_deployed
end GolfUpstream
