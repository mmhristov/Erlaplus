plugins {
    id("java")
    application
}

group = "org.erla"
version = "1.0-SNAPSHOT"

repositories {
    mavenCentral()
}

dependencies {
    testImplementation(platform("org.junit:junit-bom:5.9.1"))
    testImplementation("org.junit.jupiter:junit-jupiter")
//    implementation("org.graphstream:gs-core:1.1.1")
//    implementation("com.paypal.digraph:digraph-parser:1.0")
    implementation("org.jgrapht:jgrapht-core:1.5.2")
    implementation("org.jgrapht:jgrapht-io:1.5.2")
    implementation(files("../tlatools/dist/tla2tools.jar"))
}
    java {
        sourceCompatibility = JavaVersion.VERSION_16
        targetCompatibility = JavaVersion.VERSION_16
    }

    tasks.test {
    useJUnitPlatform()
}

application {
    mainClass = "org.erla.Main"
}