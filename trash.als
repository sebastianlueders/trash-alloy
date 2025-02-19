var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and       // guard
  after no Trash and   // effect on Trash
  File' = File - Trash // effect on File
}

pred delete [f : File] {
  not (f in Trash)   // guard
  Trash' = Trash + f // effect on Trash
  File' = File       // frame condition on File
}

pred restore [f : File] {
  f in Trash         // guard
  Trash' = Trash - f // effect on Trash
  File' = File       // frame condition on File
}

pred deleteFromTrash [f: File] {
  f in Trash  // Only delete files in trash
  Trash' = Trash - f  // Updated Trash is equal to the original Trash minus the files in trash
  File' = File - f  // Updated File no longer includes the files that were in trash
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f]))
}

run example {}
