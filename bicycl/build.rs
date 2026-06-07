//! Build and link BICYCL.

use std::{fs, process::Command};

fn main() {
  let out_dir = std::env::var("OUT_DIR").unwrap();
  println!("cargo::rerun-if-changed=c/");
  if !fs::exists(format!("{}/bicycl", &out_dir)).unwrap() {
    assert!(
      Command::new("git")
        .arg("clone")
        .arg("https://gite.lirmm.fr/crypto/bicycl.git")
        .current_dir(&out_dir)
        .status()
        .unwrap()
        .success()
    );
    assert!(
      Command::new("git")
        .arg("checkout")
        .arg("7927f9c4f5ed78af03eaed0ff7e8093e13554382")
        .current_dir(format!("{}/bicycl", &out_dir))
        .status()
        .unwrap()
        .success()
    );
  }
  if fs::exists(format!("{}/bicycl.cpp", &out_dir)).unwrap() {
    fs::remove_file(format!("{}/bicycl.cpp", &out_dir)).unwrap();
  }
  if fs::exists(format!("{}/bicycl.o", &out_dir)).unwrap() {
    fs::remove_file(format!("{}/bicycl.o", &out_dir)).unwrap();
  }
  assert!(Command::new("cp").arg("./c/bicycl.cpp").arg(&out_dir).status().unwrap().success());
  assert!(
    Command::new("c++")
      .arg("-std=c++11")
      .arg("-c")
      .arg("bicycl.cpp")
      .arg("-I")
      .arg("bicycl/src/")
      .arg("-l")
      .arg("gmp")
      .arg("-O2")
      .current_dir(&out_dir)
      .status()
      .unwrap()
      .success()
  );
  assert!(
    Command::new("ar")
      .arg("rcs")
      .arg("libbicycl.a")
      .arg("bicycl.o")
      .current_dir(&out_dir)
      .status()
      .unwrap()
      .success()
  );
  println!("cargo::rustc-link-search=native={}", &out_dir);
  println!("cargo::rustc-link-lib=bicycl");
  println!("cargo::rustc-link-lib=stdc++");
  println!("cargo::rustc-link-lib=gmp");
  println!("cargo::rustc-link-lib=gmpxx");
}
