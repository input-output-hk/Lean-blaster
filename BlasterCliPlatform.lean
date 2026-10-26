import Blaster.Cli.Platform

/-! Native services for the standalone executable. This module is outside the public Blaster library. -/
namespace Blaster.Cli.Native

@[extern "blaster_console_open"] opaque consoleOpen : IO Unit
@[extern "blaster_console_close"] opaque consoleClose : IO Unit
@[extern "blaster_report_write"] opaque reportWrite (bytes : @& ByteArray) : IO Unit
@[extern "blaster_report_tty"] opaque reportTty : BaseIO Bool
@[extern "blaster_signal"] opaque interruptSignal : BaseIO UInt32
@[extern "blaster_columns"] opaque terminalColumns : BaseIO UInt32
@[extern "blaster_clip"] opaque clipDisplay (text : @& String) (width : UInt32) : BaseIO String
@[extern "blaster_force_kill"] opaque forceKill (pid : UInt32) : IO Unit

end Blaster.Cli.Native
