#!/bin/sh
# Prove the published package works as a dependency: pack Ethereum.LeanPq into a throwaway feed,
# restore it from there alone into a fresh console project, and run that project without
# LEAN_PQ_NATIVE_PATH, so the native library is the one bundled in the package: once as a portable
# app (resolved from runtimes/<rid>/native through its deps.json) and once published for the host
# RID. Arguments go to `dotnet pack`, e.g. -p:Version=1.2.3 -p:LeanPqNativeDir=DIR.
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

dotnet pack "$script_dir/../src/Ethereum.LeanPq/Ethereum.LeanPq.csproj" -c Release -o "$feed" "$@"
package=$(ls "$feed" | grep '^Ethereum\.LeanPq\..*\.nupkg$')
version=${package#Ethereum.LeanPq.}
version=${version%.nupkg}
echo "packed Ethereum.LeanPq $version; bundled natives:"
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
using Ethereum.LeanPq;

Check(Environment.GetEnvironmentVariable("LEAN_PQ_NATIVE_PATH") is null, "LEAN_PQ_NATIVE_PATH must not be set");

byte[] message = Filled(0x42);
byte[] other = Filled(0x43);
using (XmssSecretKey xmss = XmssSecretKey.FromSeed(Filled(1)))
{
    byte[] signature = xmss.Sign(message, 0);
    Check(LeanPq.XmssVerify(xmss.GetPublicKey(), message, signature), "leanXMSS signature must verify");
    Check(!LeanPq.XmssVerify(xmss.GetPublicKey(), other, signature), "leanXMSS signature must not verify another message");
}
using (SphincsSecretKey sphincs = SphincsSecretKey.FromSeed(Filled(2)))
{
    byte[] signature = sphincs.Sign(message);
    Check(LeanPq.SphincsVerify(sphincs.GetPublicKey(), message, signature), "leanSPHINCS signature must verify");
    Check(!LeanPq.SphincsVerify(sphincs.GetPublicKey(), other, signature), "leanSPHINCS signature must not verify another message");
}
// No sidecar listens here (and Windows has none): connecting must fail cleanly.
try
{
    Sidecar.Connect("missing-leanvm-sidecar.sock").Dispose();
    throw new InvalidOperationException("connecting where no sidecar listens must fail");
}
catch (LeanPqException)
{
}

Console.WriteLine($"Ethereum.LeanPq loaded from {typeof(LeanPq).Assembly.Location}");
if (File.Exists("/proc/self/maps"))
{
    string mapped = File.ReadLines("/proc/self/maps").FirstOrDefault(line => line.Contains("liblean_pq_native"))
        ?? throw new InvalidOperationException("liblean_pq_native is not mapped");
    Console.WriteLine($"native library mapped from {mapped[mapped.IndexOf('/')..]}");
}
Console.WriteLine("signed and verified with leanXMSS and leanSPHINCS");

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
PROGRAM

dotnet build "$consumer/consumer.csproj" -c Release -o "$work/portable"
dotnet "$work/portable/consumer.dll"

rid=$(dotnet --info | sed -n 's/^ *RID: *//p' | head -n 1)
dotnet publish "$consumer/consumer.csproj" -c Release -r "$rid" --self-contained false -o "$work/published"
ls "$work/published" | grep -E '^(lib)?lean_pq_native\.'
dotnet "$work/published/consumer.dll"
echo "consumer ran against Ethereum.LeanPq $version (portable and $rid)"
