namespace Ethereum.LeanPq;

/// <summary>A checked native validation or cryptographic error from lean-pq.</summary>
public sealed class LeanPqException : Exception
{
    internal LeanPqException(string message) : base(message)
    {
    }
}
