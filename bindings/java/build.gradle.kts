plugins {
    `java-library`
    id("com.vanniktech.maven.publish") version "0.37.0"
}

group = "io.github.crate-crypto"
// Releases pass -Pversion=X.Y.Z (or ORG_GRADLE_PROJECT_version); local builds are snapshots.
version = providers.gradleProperty("version").getOrElse("0.0.0-SNAPSHOT")

repositories {
    mavenCentral()
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(25)
    }
    modularity.inferModulePath = true
}

dependencies {
    testImplementation(platform("org.junit:junit-bom:5.12.2"))
    testImplementation("org.junit.jupiter:junit-jupiter")
    testRuntimeOnly("org.junit.platform:junit-platform-launcher")
}

val osName = System.getProperty("os.name")
val nativeLibraryName = when {
    osName.startsWith("Mac") -> "liblean_pq_native.dylib"
    osName.startsWith("Windows") -> "lean_pq_native.dll"
    else -> "liblean_pq_native.so"
}
val nativeLibrary = rootProject.projectDir.resolve("../../target/release/$nativeLibraryName")

val buildNative by tasks.registering(Exec::class) {
    commandLine("cargo", "build", "--manifest-path", "../native/Cargo.toml", "--release")
}

tasks.test {
    dependsOn(buildNative)
    useJUnitPlatform()
    systemProperty("lean.pq.native.path", nativeLibrary.absolutePath)
    // Gradle executes JUnit tests on the class path. Published consumers use the narrower named
    // module permission documented in README.md.
    jvmArgs("--enable-native-access=ALL-UNNAMED")
}

// The jar carries native libraries as org/ethereum/leanpq/native/<platform>/<library>, which
// Native.java extracts and loads. Releases pass -PleanPqNativeDir=DIR, a directory already laid out
// as DIR/<platform>/<library> for every bundled platform (see scripts/build-native.sh); local builds
// bundle only the host library that buildNative produces.
val prebuiltNativeDir = providers.gradleProperty("leanPqNativeDir").map { file(it) }
val hostArch = System.getProperty("os.arch")
val hostPlatform = when {
    osName == "Linux" -> when (hostArch) {
        "amd64", "x86_64" -> "linux-x86_64"
        "aarch64" -> "linux-aarch64"
        else -> null
    }
    osName.startsWith("Mac OS X") -> "macos-universal"
    osName.startsWith("Windows") && hostArch in setOf("amd64", "x86_64") -> "windows-x86_64"
    else -> null
}

tasks.jar {
    if (prebuiltNativeDir.isPresent) {
        from(prebuiltNativeDir) { into("org/ethereum/leanpq/native") }
    } else {
        val platform = hostPlatform ?: throw GradleException(
            "lean-pq bundles no native library for $osName $hostArch; pass -PleanPqNativeDir")
        dependsOn(buildNative)
        from(nativeLibrary) { into("org/ethereum/leanpq/native/$platform") }
    }
}

mavenPublishing {
    publishToMavenCentral(automaticRelease = true)
    // Central requires signatures; local and CI builds without a key publish unsigned.
    if (providers.gradleProperty("signingInMemoryKey").isPresent) {
        signAllPublications()
    }
    coordinates(group.toString(), "lean-pq", version.toString())
    pom {
        name = "lean-pq"
        description = "Java bindings for leanVM's post-quantum signatures, leanXMSS and leanSPHINCS, " +
            "and their zkVM-backed aggregation, with bundled native libraries for Linux, macOS and Windows."
        url = "https://github.com/ethereum/lean-pq-bindings"
        licenses {
            license {
                name = "MIT License"
                url = "https://opensource.org/license/mit"
                distribution = "repo"
            }
            license {
                name = "Apache License, Version 2.0"
                url = "https://www.apache.org/licenses/LICENSE-2.0.txt"
                distribution = "repo"
            }
        }
        developers {
            developer {
                id = "crate-crypto"
                name = "Crate Crypto"
                url = "https://github.com/crate-crypto"
                organization = "Ethereum"
                organizationUrl = "https://github.com/ethereum"
            }
        }
        scm {
            url = "https://github.com/ethereum/lean-pq-bindings"
            connection = "scm:git:https://github.com/ethereum/lean-pq-bindings.git"
            developerConnection = "scm:git:ssh://git@github.com/ethereum/lean-pq-bindings.git"
        }
    }
}
