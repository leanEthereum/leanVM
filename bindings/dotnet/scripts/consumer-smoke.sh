#!/bin/sh
# Prove the published package works as a dependency: pack Ethereum.LeanPq into a throwaway feed,
# restore it from there alone into a fresh console project, and run that project, which signs,
# verifies and aggregates, without LEAN_PQ_NATIVE_PATH, so the native library is the one bundled in
# the package: once as a portable app (resolved from runtimes/<rid>/native through its deps.json)
# and once published for the host RID. Arguments go to `dotnet pack`, e.g. -p:Version=1.2.3
# -p:LeanPqNativeDir=DIR, or are `--feed DIR` to run against the one package already in DIR.
# On Windows it runs under Git Bash.
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
if command -v cygpath >/dev/null 2>&1; then
    # dotnet is a Windows program: hand it C:/... paths, which Git Bash accepts too.
    work=$(cygpath -m "$work")
fi
feed="$work/feed"
consumer="$work/consumer"
export NUGET_PACKAGES="$work/packages"
export DOTNET_CLI_TELEMETRY_OPTOUT=1
export DOTNET_NOLOGO=1
unset LEAN_PQ_NATIVE_PATH

if [ "${1:-}" = --feed ]; then
    feed=$2
    if command -v cygpath >/dev/null 2>&1; then feed=$(cygpath -m "$feed"); fi
else
    dotnet pack "$script_dir/../src/Ethereum.LeanPq/Ethereum.LeanPq.csproj" -c Release -o "$feed" "$@"
fi
package=$(ls "$feed" | grep '^Ethereum\.LeanPq\..*\.nupkg$')
version=${package#Ethereum.LeanPq.}
version=${version%.nupkg}
echo "Ethereum.LeanPq $version; bundled natives:"
unzip -Z1 "$feed/$package" | grep -E '^runtimes/[^/]+/native/(lib)?lean_pq_native\.'

mkdir -p "$consumer"
cat > "$consumer/nuget.config" <<NUGET
<?xml version="1.0" encoding="utf-8"?>
<configuration>
  <packageSources>
    <clear />
    <add key="feed" value="$feed" />
    <add key="nuget.org" value="https://api.nuget.org/v3/index.json" />
  </packageSources>
  <!-- Ethereum.LeanPq resolves only from the throwaway feed, from what was just packed. -->
  <packageSourceMapping>
    <packageSource key="feed">
      <package pattern="Ethereum.LeanPq" />
    </packageSource>
    <packageSource key="nuget.org">
      <package pattern="*" />
    </packageSource>
  </packageSourceMapping>
</configuration>
NUGET
cat > "$consumer/consumer.csproj" <<PROJECT
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <ImplicitUsings>enable</ImplicitUsings>
    <Nullable>enable</Nullable>
  </PropertyGroup>
  <ItemGroup>
    <PackageReference Include="Ethereum.LeanPq" Version="$version" />
  </ItemGroup>
</Project>
PROJECT
cat > "$consumer/Program.cs" <<'PROGRAM'
using Ethereum.PostQuantum;

Check(Environment.GetEnvironmentVariable("LEAN_PQ_NATIVE_PATH") is null, "LEAN_PQ_NATIVE_PATH must not be set");

byte[] message = Filled(0x42);
byte[] other = Filled(0x43);
using (XmssSecretKey xmss = XmssSecretKey.FromSeed(Filled(1)))
using (SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(Filled(2)))
{
    byte[] xmssSignature = xmss.Sign(message, 0);
    Check(LeanPq.XmssVerify(xmss.GetPublicKey(), message, xmssSignature), "leanXMSS signature must verify");
    Check(!LeanPq.XmssVerify(xmss.GetPublicKey(), other, xmssSignature), "leanXMSS signature must not verify another message");
    byte[] sphincsSignature = sphincs.Sign(message);
    Check(LeanPq.SphincsVerify(sphincs.GetPublicKey(), message, sphincsSignature), "leanSPHINCS signature must verify");
    Check(!LeanPq.SphincsVerify(sphincs.GetPublicKey(), other, sphincsSignature), "leanSPHINCS signature must not verify another message");

    SignatureClaim[] xmssClaims = [new(xmss.GetPublicKey(), message)];
    SignatureClaim[] sphincsClaims = [new(sphincs.GetPublicKey(), message)];
    using Aggregate aggregate = LeanPq.Aggregate(
        [],
        [new SignedMessage(xmss.GetPublicKey(), message, xmssSignature)],
        [new SignedMessage(sphincs.GetPublicKey(), message, sphincsSignature)]);
    using Aggregate received = Aggregate.FromBytes(aggregate.ToBytes(), xmssClaims, sphincsClaims);
    Check(received.GetXmssClaims().SequenceEqual(xmssClaims), "aggregate must attest the leanXMSS claim");
    Check(received.GetSphincsClaims().SequenceEqual(sphincsClaims), "aggregate must attest the leanSPHINCS claim");
}

Console.WriteLine($"Ethereum.LeanPq loaded from {typeof(LeanPq).Assembly.Location}");
if (File.Exists("/proc/self/maps"))
{
    string mapped = File.ReadLines("/proc/self/maps").FirstOrDefault(line => line.Contains("liblean_pq_native"))
        ?? throw new InvalidOperationException("liblean_pq_native is not mapped");
    Console.WriteLine($"native library mapped from {mapped[mapped.IndexOf('/')..]}");
}
Console.WriteLine("signed and verified with leanXMSS and leanSPHINCS, aggregated both");

static byte[] Filled(byte value)
{
    byte[] bytes = new byte[32];
    Array.Fill(bytes, value);
    return bytes;
}

static void Check(bool condition, string message)
{
    if (!condition)
    {
        throw new InvalidOperationException(message);
    }
}

namespace Ethereum.Client
{
    // Code in a namespace under Ethereum must reach LeanPq by its simple name.
    internal static class Names
    {
        internal const int PublicKeyLength = LeanPq.PublicKeyLength;
    }
}
PROGRAM

dotnet build "$consumer/consumer.csproj" -c Release -o "$work/portable"
dotnet "$work/portable/consumer.dll"

rid=$(dotnet --info | sed -n 's/^ *RID: *//p' | head -n 1)
dotnet publish "$consumer/consumer.csproj" -c Release -r "$rid" --self-contained false -o "$work/published"
ls "$work/published" | grep -E '^(lib)?lean_pq_native\.'
dotnet "$work/published/consumer.dll"
echo "consumer ran against Ethereum.LeanPq $version (portable and $rid)"
