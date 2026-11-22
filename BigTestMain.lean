import BigTest

/-! The big-number test as a program of its own (`big-test`). The probe can run it too, in a real enclave,
after the heartbeat the enclave's parent waits for. -/

def main : IO UInt32 := BigTest.report
