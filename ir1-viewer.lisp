;;;; ir1-viewer.lisp

(in-package #:ir1-viewer)

;;; "ir1-viewer" goes here. Hacks and glory await!
(defvar *flow-width* 800)
(defvar *flow-height* 600)
(defvar *flow-unit* 30)

(defvar *flow-x-spacing* *flow-unit*)
(defvar *flow-y-spacing* (* *flow-unit* 2))

(defvar *flow-node-width* *flow-unit*)
(defvar *flow-block-width* (* 8 *flow-unit*))

(defvar *flow-drawn-p* nil)

(defvar *copy-of-continuation-numbers* nil)
(defvar *copy-of-number-continuations* nil)

(defparameter *flow-x* (/ *flow-width* 2))
(defparameter *flow-y* *flow-y-spacing*)

(defparameter *flow-nodes* (make-hash-table))
(defparameter *flow-blocks* (make-hash-table))
(defparameter *flow-components* (make-hash-table))

(defparameter *flow-lvar-shift* 0)

;;; Graph Frame Definition
(define-application-frame ir1-viewer ()
  ((clambda :reader clambda :initarg :clambda))
  (:panes
   (flow :application
	 :display-function #'draw-flow
	 :display-time nil
	 :width *flow-width*
	 :height *flow-height*
	 :end-of-page-action :allow
	 :scroll-bars :both)
   (info :application
	 :display-time nil
	 :width *flow-width*)
   (quit :push-button
	 :label "Quit"
	 :activate-callback #'exit-viewer))
  (:layouts
   (default 
       (vertically ()
	 (horizontally ()
	   flow info)
	 quit))))

(defun exit-viewer (&rest args)
  (declare (ignore args))
  (frame-exit *application-frame*))

(defun draw-flow (frame stream)
  (setf *flow-nodes* (make-hash-table))
  (setf *flow-blocks* (make-hash-table))
  (setf *flow-components* (make-hash-table))
  
  (let ((*standard-output* stream)
	(*flow-x* *flow-x*)
	(*flow-y* *flow-y*))
    (with-drawing-options (*standard-output*)
      (let ((fail (catch :adjust-flow (present (clambda frame)) nil)))
	(case (car fail)
	  ((:x)
	   (setf *flow-x* (- *flow-x* (cdr fail)))
	   (setf *flow-y* *flow-y-spacing*))
	  ((:y)
	   (setf *flow-y* (- *flow-y* (cdr fail)))
	   (setf *flow-x* (/ *flow-width* 2))))
	(when fail
	  (redisplay-frame-pane frame stream :force-p t)))
      (setf *flow-drawn-p* t))))

(define-presentation-to-command-translator inspect-ir1 (t com-inspect-ir1 ir1-viewer) (object)
  `(,object))

(define-ir1-viewer-command com-inspect-ir1 ((ir1 't))
  (window-clear (get-frame-pane *application-frame* 'info))
  (handler-case (let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
		      (sb-c::*number-continuations* *copy-of-number-continuations*))
		  (print ir1 (get-frame-pane *application-frame* 'info)))
    (error (e) (notify-user *application-frame* (format nil "~a" e)))))

(define-ir1-viewer-command com-redisplay-ir1 ((ir1 't))
  (window-clear (get-frame-pane *application-frame* 'info))
  (handler-case (let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
		      (sb-c::*number-continuations* *copy-of-number-continuations*))
		  (print ir1 (get-frame-pane *application-frame* 'info)))
    (error (e) (notify-user *application-frame* (format nil "~a" e))))
  (window-clear (get-frame-pane *application-frame* 'flow))
  
  (setf *flow-x* 0)
  (redisplay-frame-pane *application-frame* 'flow :force-p t))

;;; Drawing Stuff
(defmacro stringify (thing)
  `(format nil "~a" ,thing))

(defmacro center-of (&rest n)
  (when n `(/ (+ ,@n) ,(length n))))

(defmacro bounding-rectangle-of (ir1)
  `(gethash ,ir1 (typecase ,ir1
		   (sb-c::node *flow-nodes*)
		   (sb-c::cblock *flow-blocks*)
		   (sb-c::component *flow-components*)
		   (t (make-hash-table)))
	    nil))

(defun create-bounding-rectangle-of (ir1 &key width height (update-flow-y t))
  (update-bounding-rectangle-of ir1
				:x1 (- *flow-x* (/ width 2))
				:y1 *flow-y*
				:x2 (+ *flow-x* (/ width 2))
				:y2 (+ *flow-y* height)
				:update-flow-y update-flow-y))

(defun update-bounding-rectangle-of (ir1 &key x1 y1 x2 y2 update-flow-y)
  (let* ((old (bounding-rectangle-of ir1))
	 (x1 (or x1 (and old (bounding-rectangle-min-x old)) (- *flow-x* (/ *flow-unit* 2))))
	 (y1 (or y1 (and old (bounding-rectangle-min-y old)) *flow-y*))
	 (x2 (or x2 (and old (bounding-rectangle-max-x old)) (+ *flow-x* (/ *flow-unit* 2))))
	 (y2 (or y2 (and old (bounding-rectangle-max-y old)) (+ *flow-y* *flow-unit*))))
    (when (some #'minusp (list x1 x2))
      (throw :adjust-flow `(:x . ,(min x1 x2))))
    (when (some #'minusp (list y1 y2))
      (throw :adjust-flow `(:y . ,(min y1 y2))))
    (prog1 (setf (bounding-rectangle-of ir1)
		 (make-bounding-rectangle x1 y1 x2 y2))
      (when update-flow-y
	(setf *flow-y* (+ (if (numberp update-flow-y)
			      update-flow-y
			      (max y1 y2))
			  *flow-y-spacing*))))))

;;; IR1 Presentation
(defmacro define-ir1-presentation-type ((&rest types) &rest args)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,@(when types
	     `((define-presentation-type ,(car types) ,@args)
	       (define-ir1-presentation-type ,(cdr types) ,@args)))
     nil))

(defmacro define-ir1-presentation-method (method-name (ir1 (type (&rest types)) &rest args) &body body)
  `(eval-when (:compile-toplevel :load-toplevel :execute)
     ,@(when types
	     `((define-presentation-method ,method-name (,ir1 (,type ,(car types)) ,@args) ,@body)
	       (define-ir1-presentation-method ,method-name (,ir1 (,type ,(cdr types)) ,@args) ,@body)))))

(define-ir1-presentation-type (sb-c::node
			       sb-c::ctran
			       sb-c::lvar
			       sb-c::cblock
			       sb-c::component
			       sb-c::clambda) ())

(define-ir1-presentation-type (sb-c::bind 
			       sb-c::cast
			       sb-c::cif
			       sb-c::combination
			       sb-c::creturn
			       sb-c::exit
			       sb-c::entry
			       sb-c::ref) () :inherit-from 'sb-c::node)

(defmacro draw-node ((node &key (width '*flow-node-width*) (height '*flow-node-width*) (minx 'min-x) (maxx 'max-x) (miny 'min-y) (maxy 'max-y)) &body body)
  (let ((n (gensym "n")))
    `(let* ((,n (create-bounding-rectangle-of ,node :width ,width :height ,height))
	    (,minx (bounding-rectangle-min-x ,n))
	    (,maxx (bounding-rectangle-max-x ,n))
	    (,miny (bounding-rectangle-min-y ,n))
	    (,maxy (bounding-rectangle-max-y ,n)))
       ,@body
       (if (eq (sb-c::block-last (sb-c::node-block ,node)) ,node)
	   (progn (update-bounding-rectangle-of (sb-c::node-block ,node) :x1 0 :y1 0 :x2 (+ (center-of ,maxx ,minx) (/ *flow-block-width* 2)) :y2 ,maxy)
		  (flet ((shift-flow-x (index total width)
			   (+ *flow-x* (* (+ *flow-x-spacing* width) (- index (if (oddp total) (/ (+ total 1) 2) (+ (/ total 2) 1/2)))))))
		    (let* ((next-blocks (sb-c::block-succ (sb-c::node-block ,node)))
			   (c (length next-blocks)))
		      (do ((next-block next-blocks (cdr next-block))
			   (i 1 (1+ i)))
			  ((null next-block))
			(let ((*flow-x* (shift-flow-x i c *flow-block-width*))
			      (*flow-y* *flow-y*))
			  (present (car next-block)))))))
	   (let ((ctran (sb-c::node-next ,node))
		 (lvar (and (typep ,node 'sb-c::valued-node) (sb-c::node-lvar ,node))))
	     (when ctran
	       (present ctran))
	     (when lvar
	       (present lvar)))))))

(define-ir1-presentation-method present (node (type (sb-c::node)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (draw-node (node)
    (draw-circle* stream
		  (center-of min-x max-x)
		  (center-of min-y max-y)
		  (center-of max-x (- min-x)))
    (draw-text* stream (stringify (type-of node))
		(+ 2 max-x)
		(center-of min-y max-y)
		:align-y :center)))

(defmacro draw-cont ((cont &key from to (fromx 'from-x) (fromy 'from-y) (tox 'to-x) (toy 'to-y) connect) &body body)
  (let ((dest (gensym "next-node"))
	(use (gensym "use-node"))
	(d (gensym "d"))
	(d-minx (gensym "d-minx"))
	(d-maxx (gensym "d-maxx"))
	(d-miny (gensym "d-miny"))
	(d-maxy (gensym "d-maxy")) 
	(u (gensym "u"))
	(u-minx (gensym "u-minx"))
	(u-maxx (gensym "u-maxx"))
	(u-miny (gensym "u-miny"))
	(u-maxy (gensym "u-maxy")))
    `(let* ((,use (if (functionp ,from) (funcall ,from ,cont) ,from))
	    (,dest (if (functionp ,to) (funcall ,to ,cont) ,to)))
       (when ,use
	 (unless (bounding-rectangle-of ,use)
	   (present ,use)))
       (when ,dest
	 (unless (bounding-rectangle-of ,dest)
	   (present ,dest)))
       (when (bounding-rectangle-of ,dest)
	 (let* ((,d (bounding-rectangle-of ,dest))
		(,d-minx (bounding-rectangle-min-x ,d))
		(,d-maxx (bounding-rectangle-max-x ,d))
		(,d-miny (bounding-rectangle-min-y ,d))
		(,d-maxy (bounding-rectangle-max-y ,d))
		(,u (when ,use (bounding-rectangle-of ,use)))
		(,u-minx (if ,u (bounding-rectangle-min-x ,u) ,d-minx))
		(,u-maxx (if ,u (bounding-rectangle-max-x ,u) ,d-maxx))
		(,u-miny (if ,u (bounding-rectangle-min-y ,u) (- ,d-miny *flow-y-spacing*)))
		(,u-maxy (if ,u (bounding-rectangle-max-y ,u) (- ,d-maxy *flow-y-spacing*)))
		(,fromx (case ,connect
			  (:left-side ,u-minx)
			  (:right-side ,u-maxx)
			  (t (center-of ,u-minx ,u-maxx))))
		(,fromy (case ,connect
			  ((:left-side :right-side) (center-of ,u-maxy ,u-miny))
			  (t ,u-maxy)))
		(,tox (case ,connect
			(:left-side ,d-minx)
			(:right-side ,d-maxx)
			(t (center-of ,d-minx ,d-maxx))))
		(,toy (case ,connect
			((:left-side :right-side) (center-of ,d-maxy ,d-miny))
			(t ,d-miny))))
	   (declare (ignorable ,d ,d-minx ,d-maxx ,d-miny ,d-maxy ,u ,u-minx ,u-maxx ,u-miny ,u-maxy ,fromx ,fromy ,tox ,toy))
	   ,@body)))))

(define-ir1-presentation-method present (ctran (type (sb-c::ctran)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (draw-cont (ctran :from #'sb-c::ctran-use :to #'sb-c::ctran-next)
    (draw-arrow* stream from-x from-y to-x to-y :ink +red+)
    (draw-text* stream (stringify (type-of ctran)) (center-of from-x to-x) (center-of from-y to-y) :align-y :center :align-x :left)
    (when (eq (sb-c::ctran-kind ctran) :block-start)
      (update-bounding-rectangle-of (sb-c::ctran-block ctran) :x1 (- from-x (/ *flow-block-width* 2)) :y1 from-y :x2 nil :y2 nil))))

(define-ir1-presentation-method present (lvar (type (sb-c::lvar)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (let* ((uses (sb-c::lvar-uses lvar))
	 (uses (if (listp uses) uses (list uses))))
    (dolist (use uses)
      (draw-cont (lvar :from use :to #'sb-c::lvar-dest :connect :left-side)
	(setf *flow-lvar-shift* (+ (* 1/3  *flow-x-spacing*) *flow-lvar-shift*))
	(draw-line* stream (- from-x *flow-lvar-shift*) (+ from-y (* 1/3 *flow-y-spacing*)) from-x from-y :ink +green+)
	(draw-line* stream (- from-x *flow-lvar-shift*) (+ from-y (* 1/3 *flow-y-spacing*)) (- to-x *flow-lvar-shift*) (- to-y (* 1/3 *flow-y-spacing*)) :ink +green+)
	(draw-arrow* stream (- to-x *flow-lvar-shift*) (- to-y (* 1/3 *flow-y-spacing*)) to-x to-y :ink +green+)
	(draw-text* stream (stringify (type-of lvar)) (- (center-of from-x to-x) *flow-lvar-shift*) (center-of from-y to-y) :align-y :center :align-x :right)))))

(define-ir1-presentation-method present (cblock (type (sb-c::cblock)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (let* ((*flow-lvar-shift* 0)
	 (start-ctran (sb-c::block-start cblock)))
    (when start-ctran
      (present start-ctran)
      (let* ((b (bounding-rectangle-of cblock))
       	     (b-minx (bounding-rectangle-min-x b))
       	     (b-maxx (bounding-rectangle-max-x b))
       	     (b-miny (bounding-rectangle-min-y b))
       	     (b-maxy (bounding-rectangle-max-y b)))
	(draw-rectangle* stream b-minx b-miny b-maxx b-maxy :filled nil)
       	(dolist (next (sb-c::block-succ cblock))
       	  (draw-cont (cblock :from cblock :to next)
	    (draw-arrow* stream from-x from-y to-x to-y :ink +blue+)))))))

(define-ir1-presentation-method present (component (type (sb-c::component)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (let* ((cblock (sb-c::block-next (sb-c::component-head component))))
    (when cblock
      (present cblock))))

(define-ir1-presentation-method present (clambda (type (sb-c::clambda)) stream view &key acceptably)
  (declare (ignorable acceptably))
  (let* ((component (sb-c::lambda-component clambda)))
    (present component (presentation-type-of component))))


;;; Top Interface
(defmacro view-ir1 (form-being-compiled)
  (let ((backup (gensym "sb-c::make-functional-from-toplevel-lambda")))
    `(progn
       (eval-when (:compile-toplevel :execute) 
	 (unlock-package (find-package :sb-c))
	 (let ((,backup (symbol-function 'sb-c::make-functional-from-toplevel-lambda)))
	   (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda)
		 (lambda (lambda-expression &key name (path (sb-c::missing-arg)))
		   (format *terminal-io* "compiling ~a~%" lambda-expression)
		   (let ((clambda (funcall ,backup lambda-expression :name name :path path)))
		     (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) ,backup)
		     (setf *copy-of-continuation-numbers* sb-c::*continuation-numbers*)
		     (setf *copy-of-number-continuations* sb-c::*number-continuations*)
		     (clim-sys:make-process (lambda () (run-frame-top-level (make-instance 'ir1-viewer :clambda clambda))))
		     (clim-sys:process-wait-with-timeout "Drawing IR1 Flow" 1 (lambda () *flow-drawn-p*))
		     (setf *flow-drawn-p* nil)
		     (format *terminal-io* "~a~%" clambda)
		     clambda)))))
       ,form-being-compiled)))