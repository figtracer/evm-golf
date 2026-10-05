import EvmYul.EVM.Semantics
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open EvmYul EvmYul.EVM
namespace GolfOpcodeDecode

theorem decode_mul (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 2)) :
    decode code pc = some ((Operation.MUL : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_shl (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 27)) :
    decode code pc = some ((Operation.SHL : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_add (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 1)) :
    decode code pc = some ((Operation.ADD : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_swap1 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 144)) :
    decode code pc = some ((Operation.SWAP1 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push0 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 95)) :
    decode code pc = some ((Operation.PUSH0 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_dup1 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 128)) :
    decode code pc = some ((Operation.DUP1 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_sub (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 3)) :
    decode code pc = some ((Operation.SUB : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_and (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 22)) :
    decode code pc = some ((Operation.AND : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_not (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 25)) :
    decode code pc = some ((Operation.NOT : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_lt (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 16)) :
    decode code pc = some ((Operation.LT : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_iszero (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 21)) :
    decode code pc = some ((Operation.ISZERO : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_lt
#print axioms decode_iszero
#print axioms decode_mul
#print axioms decode_shl
#print axioms decode_add
#print axioms decode_swap1
#print axioms decode_push0
#print axioms decode_dup1
#print axioms decode_sub
#print axioms decode_and
#print axioms decode_not
theorem decode_or (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 23)) :
    decode code pc = some ((Operation.OR : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_or

theorem decode_swap2 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 145)) :
    decode code pc = some ((Operation.SWAP2 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap2

theorem decode_swap3 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 146)) :
    decode code pc = some ((Operation.SWAP3 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap3

theorem decode_swap4 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 147)) :
    decode code pc = some ((Operation.SWAP4 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap4

theorem decode_swap5 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 148)) :
    decode code pc = some ((Operation.SWAP5 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap5

theorem decode_swap6 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 149)) :
    decode code pc = some ((Operation.SWAP6 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap6

theorem decode_swap7 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 150)) :
    decode code pc = some ((Operation.SWAP7 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap7

theorem decode_swap8 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 151)) :
    decode code pc = some ((Operation.SWAP8 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap8

theorem decode_swap9 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 152)) :
    decode code pc = some ((Operation.SWAP9 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap9

theorem decode_swap10 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 153)) :
    decode code pc = some ((Operation.SWAP10 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap10

theorem decode_swap11 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 154)) :
    decode code pc = some ((Operation.SWAP11 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap11

theorem decode_swap12 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 155)) :
    decode code pc = some ((Operation.SWAP12 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap12

theorem decode_swap13 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 156)) :
    decode code pc = some ((Operation.SWAP13 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap13

theorem decode_swap14 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 157)) :
    decode code pc = some ((Operation.SWAP14 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap14

theorem decode_swap15 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 158)) :
    decode code pc = some ((Operation.SWAP15 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap15

theorem decode_swap16 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 159)) :
    decode code pc = some ((Operation.SWAP16 : Operation .EVM), none) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_swap16

end GolfOpcodeDecode

namespace GolfOpcodeDecode

theorem decode_push1 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 96)) :
    decode code pc = some ((Operation.Push .PUSH1 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push2 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 97)) :
    decode code pc = some ((Operation.Push .PUSH2 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 2)), 2)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push3 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 98)) :
    decode code pc = some ((Operation.Push .PUSH3 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 3)), 3)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push4 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 99)) :
    decode code pc = some ((Operation.Push .PUSH4 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 4)), 4)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push5 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 100)) :
    decode code pc = some ((Operation.Push .PUSH5 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 5)), 5)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push6 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 101)) :
    decode code pc = some ((Operation.Push .PUSH6 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 6)), 6)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push7 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 102)) :
    decode code pc = some ((Operation.Push .PUSH7 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 7)), 7)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push8 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 103)) :
    decode code pc = some ((Operation.Push .PUSH8 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 8)), 8)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push9 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 104)) :
    decode code pc = some ((Operation.Push .PUSH9 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 9)), 9)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push10 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 105)) :
    decode code pc = some ((Operation.Push .PUSH10 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 10)), 10)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push11 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 106)) :
    decode code pc = some ((Operation.Push .PUSH11 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 11)), 11)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push12 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 107)) :
    decode code pc = some ((Operation.Push .PUSH12 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 12)), 12)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push13 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 108)) :
    decode code pc = some ((Operation.Push .PUSH13 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 13)), 13)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push14 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 109)) :
    decode code pc = some ((Operation.Push .PUSH14 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 14)), 14)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push15 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 110)) :
    decode code pc = some ((Operation.Push .PUSH15 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 15)), 15)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push16 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 111)) :
    decode code pc = some ((Operation.Push .PUSH16 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 16)), 16)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push17 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 112)) :
    decode code pc = some ((Operation.Push .PUSH17 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 17)), 17)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push18 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 113)) :
    decode code pc = some ((Operation.Push .PUSH18 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 18)), 18)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push19 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 114)) :
    decode code pc = some ((Operation.Push .PUSH19 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 19)), 19)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push20 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 115)) :
    decode code pc = some ((Operation.Push .PUSH20 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 20)), 20)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push21 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 116)) :
    decode code pc = some ((Operation.Push .PUSH21 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 21)), 21)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push22 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 117)) :
    decode code pc = some ((Operation.Push .PUSH22 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 22)), 22)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push23 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 118)) :
    decode code pc = some ((Operation.Push .PUSH23 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 23)), 23)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push24 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 119)) :
    decode code pc = some ((Operation.Push .PUSH24 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 24)), 24)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push25 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 120)) :
    decode code pc = some ((Operation.Push .PUSH25 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 25)), 25)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push26 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 121)) :
    decode code pc = some ((Operation.Push .PUSH26 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 26)), 26)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push27 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 122)) :
    decode code pc = some ((Operation.Push .PUSH27 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 27)), 27)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push28 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 123)) :
    decode code pc = some ((Operation.Push .PUSH28 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 28)), 28)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push29 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 124)) :
    decode code pc = some ((Operation.Push .PUSH29 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 29)), 29)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push30 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 125)) :
    decode code pc = some ((Operation.Push .PUSH30 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 30)), 30)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push31 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 126)) :
    decode code pc = some ((Operation.Push .PUSH31 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 31)), 31)) := by
  unfold decode
  rw [fetched]
  rfl

theorem decode_push32 (code : ByteArray) (pc : UInt256)
    (fetched : code.get? pc.toNat = some (UInt8.ofNat 127)) :
    decode code pc = some ((Operation.Push .PUSH32 : Operation .EVM),
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 32)), 32)) := by
  unfold decode
  rw [fetched]
  rfl

#print axioms decode_push1
#print axioms decode_push2
#print axioms decode_push3
#print axioms decode_push4
#print axioms decode_push5
#print axioms decode_push6
#print axioms decode_push7
#print axioms decode_push8
#print axioms decode_push9
#print axioms decode_push10
#print axioms decode_push11
#print axioms decode_push12
#print axioms decode_push13
#print axioms decode_push14
#print axioms decode_push15
#print axioms decode_push16
#print axioms decode_push17
#print axioms decode_push18
#print axioms decode_push19
#print axioms decode_push20
#print axioms decode_push21
#print axioms decode_push22
#print axioms decode_push23
#print axioms decode_push24
#print axioms decode_push25
#print axioms decode_push26
#print axioms decode_push27
#print axioms decode_push28
#print axioms decode_push29
#print axioms decode_push30
#print axioms decode_push31
#print axioms decode_push32
end GolfOpcodeDecode
