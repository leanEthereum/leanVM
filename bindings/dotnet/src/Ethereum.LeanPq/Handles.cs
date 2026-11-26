using Microsoft.Win32.SafeHandles;

namespace Ethereum.PostQuantum;

// SafeHandle counts every P/Invoke using it, so a handle disposed on another thread is destroyed
// only once those calls return; an undisposed one is destroyed by its finalizer.

internal sealed class XmssKeyHandle() : SafeHandleZeroOrMinusOneIsInvalid(ownsHandle: true)
{
    protected override bool ReleaseHandle()
    {
        Native.XmssDestroy(handle);
        return true;
    }
}

internal sealed class SphincsKeyHandle() : SafeHandleZeroOrMinusOneIsInvalid(ownsHandle: true)
{
    protected override bool ReleaseHandle()
    {
        Native.SphincsDestroy(handle);
        return true;
    }
}

internal sealed class VrfKeyHandle() : SafeHandleZeroOrMinusOneIsInvalid(ownsHandle: true)
{
    protected override bool ReleaseHandle()
    {
        Native.VrfKeyDestroy(handle);
        return true;
    }
}

internal sealed class AggregateHandle() : SafeHandleZeroOrMinusOneIsInvalid(ownsHandle: true)
{
    protected override bool ReleaseHandle()
    {
        Native.AggregateDestroy(handle);
        return true;
    }
}
