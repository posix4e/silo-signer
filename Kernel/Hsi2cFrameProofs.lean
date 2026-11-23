import Kernel.Hsi2cFrame

/-! # A read changes no chip's registers, and a stopped bus is left alone (`Kernel.Hsi2cFrameProofs`)

1. `plan_writes_only_the_register_number`: every transfer of a read's plan puts at most one byte on the bus
   after the chip's address, and that byte is the number of the register asked for. A chip's register is
   changed by a second byte, which is never sent.
2. `plan_reads_within_the_queue`: the read asks for at least one byte and no more than the controller's
   queue is trusted to hold.
3. `plan_ends_with_a_stop`: the plan's last transfer releases the bus.
4. `mayTouch_needs_running_clocks`: the controller is read only if both of its clock gates are open and
   neither may be closed by the hardware by itself.
5. `mayTouch_needs_i2c`: and only if its serial block is set to speak I2C.
6. `running_refuses_automatic_gating`: a gate the hardware may close counts as closed, whatever else it says.
7. `running_refuses_closed`: so does a gate that is not open. -/

namespace Kernel.Hsi2cFrameProofs

open Kernel.Hsi2cFrame

theorem plan_writes_only_the_register_number (chip reg : UInt8) (n : Nat) :
    ∀ x ∈ plan chip reg n, x.written = [reg] ∨ x.written = [] := by
  intro x hx
  simp [plan] at hx
  rcases hx with h | h <;> simp [h, Xfer.written]

theorem plan_reads_within_the_queue (chip reg : UInt8) (n : Nat) :
    ∀ c s, Xfer.read chip c s ∈ plan chip reg n → 1 ≤ c ∧ c ≤ maxRead := by
  intro c s h
  simp [plan] at h
  obtain ⟨hc, _⟩ := h
  subst hc
  simp [clampCount, maxRead]
  omega

theorem plan_ends_with_a_stop (chip reg : UInt8) (n : Nat) :
    (plan chip reg n).getLast? = some (.read chip (clampCount n) true) := by
  simp [plan]

theorem mayTouch_needs_running_clocks (g : Gates) (h : g.mayTouch = true) :
    running g.ipclk = true ∧ running g.pclk = true := by
  simp only [Gates.mayTouch, Gates.verdict] at h
  by_cases h1 : running g.ipclk = true
  · by_cases h2 : running g.pclk = true
    · exact ⟨h1, h2⟩
    · simp [h1, h2] at h
  · simp [h1] at h

theorem mayTouch_needs_i2c (g : Gates) (h : g.mayTouch = true) : g.mode &&& 7 = modeI2c := by
  simp only [Gates.mayTouch, Gates.verdict] at h
  by_cases h1 : running g.ipclk = true
  · by_cases h2 : running g.pclk = true
    · by_cases h3 : g.mode &&& 7 = modeI2c
      · exact h3
      · simp [h1, h2, h3] at h
    · simp [h1, h2] at h
  · simp [h1] at h

theorem running_refuses_automatic_gating (gate : UInt32) (h : gate &&& 0x10000000 ≠ 0) :
    running gate = false := by
  simp [running, h]

theorem running_refuses_closed (gate : UInt32) (h : gate &&& 0x00200000 = 0) :
    running gate = false := by
  simp [running, h]

end Kernel.Hsi2cFrameProofs
