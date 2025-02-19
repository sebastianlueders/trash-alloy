var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash     // guard to ensure that there are files in trash
  after no Trash  // No files in Trash after effect
  File' = File - Trash // File no longer includes files in Trash
}

pred delete [f : File] {
  not (f in Trash)   // guard to ensure that f is not in the Trash 
  Trash' = Trash + f // Ensures that f is added to Trash from this action
  File' = File       // Frame condition to show that File signature is unchanged
}

pred restore [f : File] {
  f in Trash         // guard to ensure that f is in Trash
  Trash' = Trash - f // f is removed from the Trash signature
  File' = File       // Frame condition to show that File remains unchanged from this action
}

pred deleteFromTrash [f : File] {
  f in Trash and f in File  // guard to ensure that f is in the trash and file signatures
  Trash' = Trash - f  // f no longer in Trash
  File' = File - f // f no longer in File
}

pred deleteOutsideTrash [f : File] {
  f not in Trash  // guard to ensure f is not in Trash
  f in File    // guard to ensure f is still in File
  Trash' = Trash  // Frame condition
  File' = File - f  // f removed from Trash
}

pred duplicate [f : File] {
  f in File  // guard to ensure that f is in File and/or Trash
  File' = File + f  // f added to File again (represents duplicate f)
  Trash' = Trash   // Trash will remain the same since we'll never duplicate to trash
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f] or deleteFromTrash[f] or deleteOutsideTrash[f] or duplicate[f]))
  // Limits our trace to show that these are the only possible transitions in our system
  // "some f" picks a file to be deleted, restored, etc. at each state
}

assert restore_after_delete {
  always (all f : File | restore[f] implies once delete[f])
}

assert delete_all {
  always ((Trash = File and empty) implies after always no File)
}

check neverEmptyFileSignature {always some File} for 15

check emptyFileSignaturePossible {eventually no File} for 15

check delete_all for 15 steps

check restore_after_delete for 3 but 20 steps

run example {}


