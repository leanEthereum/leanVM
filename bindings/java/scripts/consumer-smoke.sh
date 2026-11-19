#!/bin/sh
# Prove the published artifact works as a dependency: publish io.github.crate-crypto:lean-pq to a
# throwaway Maven repository, resolve it from there in a fresh modular Gradle project, and run that
# project on the module path with --enable-native-access=org.ethereum.leanpq and no
# lean.pq.native.path, so the native library is the one bundled in the jar.
# Arguments go to the publishing build, e.g. -Pversion=1.2.3 -PleanPqNativeDir=DIR.
# GRADLE names the Gradle command (default `gradle`); JAVA_HOME selects the JDK 25 to run with.
# On Windows it runs under Git Bash; there it also checks that the DLL was installed once into the
# per-user cache and reused by a second run.
set -eu

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
gradle=${GRADLE:-gradle}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
jdk_bin=${JAVA_HOME:+$JAVA_HOME/bin/}
windows=false
if command -v cygpath >/dev/null 2>&1; then
    windows=true
    # Gradle and the JVM are Windows programs: hand them C:/... paths, which Git Bash accepts too.
    work=$(cygpath -m "$work")
    jdk_bin=${JAVA_HOME:+$(cygpath -u "$JAVA_HOME")/bin/}
fi
repo="$work/repo"
consumer="$work/consumer"

"$gradle" -p "$script_dir/.." publishToMavenLocal -Dmaven.repo.local="$repo" "$@"
version=$(ls "$repo/io/github/crate-crypto/lean-pq" | grep -v '^maven-metadata')
published="$repo/io/github/crate-crypto/lean-pq/$version/lean-pq-$version.jar"
echo "published io.github.crate-crypto:lean-pq:$version; bundled natives:"
"${jdk_bin}jar" tf "$published" | grep -E '^org/ethereum/leanpq/native/[^/]+/(lib)?lean_pq_native\.'

mkdir -p "$consumer/src/main/java/consumer"
cat > "$consumer/settings.gradle.kts" <<EOF
rootProject.name = "consumer"
dependencyResolutionManagement {
    // Only the throwaway repository: the artifact must resolve from what was just published.
    repositories { maven { url = uri("$repo") } }
}
EOF
cat > "$consumer/build.gradle.kts" <<EOF
plugins { application }
java { toolchain { languageVersion = JavaLanguageVersion.of(25) } }
dependencies { implementation("io.github.crate-crypto:lean-pq:$version") }
application {
    mainModule = "consumer"
    mainClass = "consumer.Main"
}
EOF
cat > "$consumer/src/main/java/module-info.java" <<'EOF'
module consumer {
    requires org.ethereum.leanpq;
}
EOF
cat > "$consumer/src/main/java/consumer/Main.java" <<'EOF'
package consumer;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import org.ethereum.leanpq.LeanPq;
import org.ethereum.leanpq.LeanPqException;
import org.ethereum.leanpq.Sidecar;
import org.ethereum.leanpq.SphincsSecretKey;
import org.ethereum.leanpq.XmssSecretKey;

public final class Main {
    public static void main(String[] args) throws Exception {
        check(System.getProperty("lean.pq.native.path") == null, "lean.pq.native.path must not be set");
        Module module = LeanPq.class.getModule();
        check(module.isNamed() && module.isNativeAccessEnabled(), "org.ethereum.leanpq must be a named module with native access");

        byte[] message = filled(0x42);
        byte[] other = filled(0x43);
        try (XmssSecretKey xmss = XmssSecretKey.fromSeed(filled(1));
             SphincsSecretKey sphincs = SphincsSecretKey.fromSeed(filled(2))) {
            byte[] xmssSignature = xmss.sign(message, 0);
            check(LeanPq.xmssVerify(xmss.publicKey(), message, xmssSignature), "leanXMSS signature must verify");
            check(!LeanPq.xmssVerify(xmss.publicKey(), other, xmssSignature), "leanXMSS signature must not verify another message");
            byte[] sphincsSignature = sphincs.sign(message);
            check(LeanPq.sphincsVerify(sphincs.publicKey(), message, sphincsSignature), "leanSPHINCS signature must verify");
            check(!LeanPq.sphincsVerify(sphincs.publicKey(), other, sphincsSignature), "leanSPHINCS signature must not verify another message");
        }
        // No sidecar listens here (and Windows has none): connecting must fail cleanly.
        try {
            Sidecar.connect(Path.of("missing-leanvm-sidecar.sock")).close();
            throw new AssertionError("connecting where no sidecar listens must fail");
        } catch (LeanPqException expected) {
        }

        System.out.println("module " + module.getName() + " loaded from " + LeanPq.class.getProtectionDomain().getCodeSource().getLocation());
        Path maps = Path.of("/proc/self/maps");
        if (Files.exists(maps)) {
            String mapped = Files.readAllLines(maps).stream()
                .filter(line -> line.contains("liblean_pq_native"))
                .map(line -> line.substring(line.indexOf('/')))
                .findFirst()
                .orElseThrow(() -> new AssertionError("liblean_pq_native is not mapped"));
            System.out.println("native library mapped from " + mapped);
        }
        System.out.println("signed and verified with leanXMSS and leanSPHINCS");
    }

    private static byte[] filled(int value) {
        byte[] bytes = new byte[32];
        Arrays.fill(bytes, (byte) value);
        return bytes;
    }

    private static void check(boolean condition, String message) {
        if (!condition) {
            throw new AssertionError(message);
        }
    }
}
EOF

"$gradle" -p "$consumer" installDist
lib="$consumer/build/install/consumer/lib"
cmp "$published" "$lib/lean-pq-$version.jar"
# --illegal-native-access=deny turns a missing or misnamed native-access grant into an error.
run_consumer() {
    "${jdk_bin}java" --enable-native-access=org.ethereum.leanpq --illegal-native-access=deny -p "$lib" -m consumer/consumer.Main
}
run_consumer
if [ "$windows" = true ]; then
    # Windows cannot delete a loaded DLL, so Native.java installs it once per build under
    # %LOCALAPPDATA%\lean-pq\native\<sha256>\; a second JVM must reuse that copy, not add another.
    dll=org/ethereum/leanpq/native/windows-x86_64/lean_pq_native.dll
    (cd "$work" && "${jdk_bin}jar" xf "$published" "$dll")
    digest=$(sha256sum "$work/$dll" | cut -d ' ' -f 1)
    cache="$(cygpath -u "$LOCALAPPDATA")/lean-pq/native/$digest"
    test "$(ls -A "$cache")" = lean_pq_native.dll
    cmp "$work/$dll" "$cache/lean_pq_native.dll"
    installed=$(stat -c '%i %Y' "$cache/lean_pq_native.dll")
    run_consumer
    test "$(ls -A "$cache")" = lean_pq_native.dll
    test "$(stat -c '%i %Y' "$cache/lean_pq_native.dll")" = "$installed"
    echo "both runs loaded the cached $(cygpath -w "$cache/lean_pq_native.dll")"
fi
echo "consumer ran against io.github.crate-crypto:lean-pq:$version"
