
var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}


pred delete[f : File] {
  f not in Trash
  Trash' = Trash + f
  File' = File
}


pred restore[f : File] {
  f in Trash
  Trash' = Trash - f
  File' = File
}

pred empty {
  some Trash
  Trash' = none
  File' = File - Trash
}

pred deleteFromTrash[f : File] {
  f in Trash
  Trash' = Trash - f
  File' = File - f
}

pred forceDelete[f: File] {
  f not in Trash
  Trash' = Trash
  File' = File - f
}

assert RestoreProperty {
  all f: File | delete[f] => eventually restore[f]
}

assert TrashPersistence {
  all f: File | f in Trash implies always (f in Trash or empty)
}

fact layout {
  all f: File | f in Trash => f in File
}

fact trans {
  always (empty or (some f : File | delete[f] or restore[f] or deleteFromTrash[f] or forceDelete[f]))
}



run example {} for 10

check canBeEmpty {
  once no Trash
} for 10 File, 10 steps

check EventuallyNonEmpty {
  eventually some Trash
} for 10 File, 10 steps