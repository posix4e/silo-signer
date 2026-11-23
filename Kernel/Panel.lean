import Kernel.Hw
import Kernel.Komodo

/-! # Making the panel dark (`Kernel.Panel`)

The hardware side of `Kernel.Idle`. Dark means a black picture: every pixel of the frame buffer is written
black and, on the Pixel, the display controller is asked once to send that frame to the panel. On an OLED a
black pixel is an unlit one, so this is most of what the panel draws.

It is not the panel switched off. The panel's own controller, the display controller (DECON) and the link
between them stay powered and clocked. No display-off or sleep command is sent, and no supply is touched:
this signer has no driver for the link those commands travel on, and could not bring the panel back from
them. Lighting the panel again is an ordinary redraw. -/

namespace Kernel.Panel

/-- One black pixel, which the blit stretches over the whole frame buffer. -/
private def blackPixel : ByteArray := ByteArray.mk #[0, 0, 0, 0xFF]

/-- Writes the whole frame buffer black and, where there is a display controller to ask, sends the frame. -/
def dark (deconBase? : Option UInt64) : BaseIO Unit := do
  Hw.fbBlitRgba blackPixel 1 1 1
  if let some decon := deconBase? then
    Komodo.deconFlushFrame decon

end Kernel.Panel
