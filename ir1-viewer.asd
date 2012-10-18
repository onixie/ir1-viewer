;;;; ir1-viewer.asd

(asdf:defsystem #:ir1-viewer
  :serial t
  :description "IR1 (a.k.a ICR) Viewer for SBCL Compiler"
  :author "onixie@gmail.com"
  :license "public domain"
  :depends-on (#:mcclim)
  :components ((:file "package")
               (:file "ir1-viewer")))

