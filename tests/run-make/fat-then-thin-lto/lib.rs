#![allow(internal_features)]
#![feature(no_core, lang_items)]
#![no_core]
#![crate_type = "rlib"]

#[lang = "pointee_sized"]
trait PointeeSized {}
#[lang = "meta_sized"]
trait MetaSized: PointeeSized {}
#[lang = "sized"]
trait Sized: MetaSized {}

pub fn foo() {}
