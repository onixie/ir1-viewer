;;;; ir1-viewer.lisp

(in-package #:ir1-viewer)

;;; "ir1-viewer" goes here. Hacks and glory await!

;;; Flow Stuffs
(eval-when (:compile-toplevel :load-toplevel :execute)
  (let ((display (xlib::open-default-display)))
    (defvar *screen-width* (xlib::screen-width (xlib::display-default-screen display)))
    (defvar *screen-height* (xlib::screen-height (xlib::display-default-screen display)))
    (xlib::close-display display)))

(defvar *flow-width* (/ *screen-width* 2))
(defvar *flow-height* *screen-height*)

(defvar *flow-unit* 30)
(defvar *flow-x-spacing* *flow-unit*)
(defvar *flow-y-spacing* (* *flow-unit* 2))

(defvar *copy-of-continuation-numbers* nil)
(defvar *copy-of-number-continuations* nil)

(defparameter *flow-current-x* 0)
(defparameter *flow-current-y* 0)

(defvar *ir1-flow* (make-hash-table))

;;; Utilities
(defmacro center-of (&rest n)
  (when n `(the real (/ (+ ,@n) ,(length n)))))

(defmacro ensure-list (thing)
  `(or (and (listp ,thing) ,thing) (list ,thing)))

(defmacro print-log (&rest args)
  `(format *terminal-io* "~&~a~%" (format nil ,@args)))

(defmacro define-alias (alias name)
  (if (macro-function name)
      (progn
	(setf (macro-function alias) (macro-function name))
	`(load-time-value (setf (macro-function ',alias) (macro-function ',name))))
      (progn
	(setf (symbol-function alias) (symbol-function name))
	`(load-time-value (setf (symbol-function ',alias) (symbol-function ',name))))))

(define-alias min-x bounding-rectangle-min-x)
(define-alias max-x bounding-rectangle-max-x)
(define-alias min-y bounding-rectangle-min-y)
(define-alias max-y bounding-rectangle-max-y)

(defun map-over-polyline (func polyline)
  (declare (type (function (real real real real) *) func)
	   (type polyline polyline))
  (let ((line 1))
    (map-over-polygon-segments
     (lambda (&rest xy)
       (when (oddp line)
	 (apply func xy))
       (incf line))
     polyline))
  nil)

(defun line-middle-point (line)
  (multiple-value-bind (sx sy) (line-start-point* line)
    (multiple-value-bind (ex ey) (line-end-point* line)
      (make-point (center-of sx ex) (center-of sy ey)))))

(defmacro size-of ((stream) &body body)
  `(let ((record (with-output-to-output-record (,stream)
		   ,@body)))
     (bounding-rectangle-size record)))

;;; IR1 Regions
(defvar *recompute-p* nil)
(defvar *ir1-flow* nil)

(defun make-ir1-flow (clambda)
  (labels ((make (clambda)
	     (let ((flow-original-x *flow-current-x*)
		   (flow-original-y *flow-current-y*)
		   (*flow-current-x* *flow-current-x*)
		   (*flow-current-y* *flow-current-y*)
		   (*ir1-flow* (make-hash-table)))
	       (let ((clambda-region (region-ir1 clambda)))
		 (when (minusp (min-x clambda-region))
		   (setf *flow-current-x* (- flow-original-x (min-x clambda-region))))
		 (when (minusp (min-y clambda-region))
		   (setf *flow-current-y* (- flow-original-y (min-y clambda-region))))
		 (region-ir1 clambda :recompute-p :recursive))
	       (cons clambda *ir1-flow*)))
	   (top-of (clambda)
	     (if (sb-c::lambda-parent clambda)
		 (top-of (sb-c::lambda-parent clambda))
		 clambda))
	   (descended-of (clambda)
	     (when clambda
	       (cons clambda (mapcan #'descended-of (sb-c::lambda-children clambda))))))
    (let ((clambdas (remove-duplicates (append (descended-of (top-of clambda))
					       (list (sb-c::lambda-entry-fun clambda))
					       (sb-c::lambda-lets clambda)
					       (sb-c::tail-set-funs (sb-c::lambda-tail-set clambda))
					       (remove-if-not #'sb-c::functional-p (concatenate 'list (sb-c::sset-vector (sb-c::lambda-calls-or-closes clambda))))))))
      (mapcar #'make clambdas))))

(defun valid-region-p (region)
  (and region (not (eq region +nowhere+)) region))

(defmacro with-valid-region (region &body body)
  `(awhen (valid-region-p ,region)
     ,@body))

(defun margined-region (region &key (x-ratio 1) (y-ratio 1))
  (if (valid-region-p region)
      (make-bounding-rectangle (- (min-x region) (* x-ratio *flow-x-spacing*))
			       (- (min-y region) (* y-ratio *flow-y-spacing*))
			       (+ (max-x region) (* x-ratio *flow-x-spacing*))
			       (+ (max-y region) (* y-ratio *flow-y-spacing*)))
      region))

(defmacro define-ir1-region ((ir1 &key (recursively-recompute-p t)) &body body)
  `(defun ,(symbolicate 'region- ir1) (,ir1 &key (recompute-p *recompute-p*) (ir1-flow *ir1-flow*))
     (if ,ir1
	 (or (and (not recompute-p) (gethash ,ir1 ir1-flow nil))
	     (setf (gethash ,ir1 ir1-flow)
		   (let ((*recompute-p* (and ,recursively-recompute-p 
					     (eq recompute-p :recursive) 
					     :recursive))
			 (*ir1-flow* ir1-flow))
		     ,@body)))
	 +nowhere+)))

(define-ir1-region (ir1)
  (typecase ir1
    (sb-c::clambda (region-clambda ir1))
    (sb-c::component (region-component ir1))
    (sb-c::cblock (region-cblock ir1))
    (sb-c::ctran (region-ctran ir1))
    (sb-c::lvar (region-lvar ir1))
    (sb-c::node (region-node ir1))
    (t +nowhere+)))

(define-ir1-region (clambda) 
  (margined-region (region-component (sb-c::lambda-component clambda))))

(define-ir1-region (component) 
  (let ((flow-original-x *flow-current-x*))
    (labels ((region-cblocks (cblock-head region)
	       (let ((*flow-current-x* *flow-current-x*))
		 (do* ((cblocks (next-of cblock-head) (rest cblocks))
		       (cblock (first cblocks) (first cblocks)))
		      ((null cblocks) region)
		   (let* ((*flow-current-y* *flow-current-y*)
			  (cblock-region (region-cblock cblock))
			  (cblock-succ-region (region-cblocks cblock region)))
		     (setf region (region-union cblock-region cblock-succ-region))
		     (when (valid-region-p region)
		       (setf *flow-current-x* (+ flow-original-x
						 (bounding-rectangle-width region)
						 *flow-x-spacing*)))))))
	     (region-lvars (cblock-head)
	       (do ((cblocks (next-of cblock-head) (rest cblocks)))
		   ((null cblocks))
		 (do* ((ctran (sb-c::block-start (first cblocks)) (next-of node))
		       (node (next-of ctran) (next-of ctran))
		       (lvar (and (sb-c::valued-node-p node) (sb-c::node-lvar node)) (and (sb-c::valued-node-p node) (sb-c::node-lvar node))))
		      ((null ctran))
		   (region-lvar lvar))
		 (region-lvars (first cblocks)))))
      (prog1 (margined-region (region-cblocks (sb-c::component-head component) +nowhere+))
	(region-lvars (sb-c::component-head component))))))

(define-ir1-region (cblock)
  (do* ((region +nowhere+ (region-union region (region-union (region-node node) (bounding-rectangle (region-ctran ctran)))))
	(ctran (sb-c::block-start cblock) (next-of node))
	(node (next-of ctran) (next-of ctran)))
       ((null ctran) (margined-region region :x-ratio 2 :y-ratio 0))))

(define-ir1-region (ctran :recursively-recompute-p nil)
  (let ((use (unless (eq (sb-c::ctran-kind ctran) :block-start)
	       (region-node (previous-of ctran))))
	(dest (region-node (next-of ctran))))
    (if use
	(make-line* (center-of (max-x use) (min-x use))
		    (max-y use)
		    (center-of (max-x dest) (min-x dest))
		    (min-y dest))
	(make-line* (center-of (max-x dest) (min-x dest))
		    (- (min-y dest) *flow-y-spacing*)
		    (center-of (max-x dest) (min-x dest))
		    (min-y dest)))))

(define-ir1-region (lvar :recursively-recompute-p nil)
  (let ((uses (mapcar (lambda (node) (region-node node)) (previous-of lvar)))
	(dest (region-node (next-of lvar))))
    (make-polyline*
     (loop for use in uses
	append (cond ((<= (min-x dest) (min-x use) (max-x dest))
		      (list (min-x use)
			    (center-of (min-y use) (max-y use))
			    (min-x dest)
			    (center-of (min-y dest) (max-y dest))))
		     ((> (min-x use) (max-x dest))
		      (list (min-x use)
			    (center-of (min-y use) (max-y use))
			    (max-x dest)
			    (center-of (min-y dest) (max-y dest))))
		     ((<= (min-x dest) (max-x use) (max-x dest))
		      (list (max-x use)
			    (center-of (min-y use) (max-y use))
			    (max-x dest)
			    (center-of (min-y dest) (max-y dest))))
		     ((< (max-x use) (min-x dest))
		      (list (max-x use)
			    (center-of (min-y use) (max-y use))
			    (min-x dest)
			    (center-of (min-y dest) (max-y dest))))))
     :closed nil)))

(define-ir1-region (node :recursively-recompute-p nil)
  (setf *flow-current-y* (+ *flow-current-y* *flow-unit*))
  (prog1 (make-bounding-rectangle (- *flow-current-x* (/ *flow-unit* 2))
				  *flow-current-y*
				  (+ *flow-current-x* (/ *flow-unit* 2))
				  (+ *flow-current-y* *flow-unit*))
    (setf *flow-current-y* (+ *flow-current-y* *flow-y-spacing*))
    (when (eq node (sb-c::block-last (sb-c::node-block node)))
      (setf *flow-current-y* (+ *flow-current-y* *flow-y-spacing*)))))

(defun previous-of (ir1)
  (typecase ir1
    (sb-c::ctran (unless (eq (sb-c::ctran-kind ir1) :block-start) (sb-c::ctran-use ir1)))
    (sb-c::node (sb-c::node-prev ir1))
    (sb-c::lvar (ensure-list (sb-c::lvar-uses ir1)))
    (sb-c::cblock (sb-c::block-pred ir1))
    (t nil)))

(defun next-of (ir1)
  (typecase ir1
    (sb-c::ctran (sb-c::ctran-next ir1))
    (sb-c::node (sb-c::node-next ir1))
    (sb-c::lvar (sb-c::lvar-dest ir1))
    (sb-c::cblock (sb-c::block-succ ir1))
    (t nil)))

;;; Clim
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass flow-view (gadget-view) ())
  (defparameter +flow-view+ (make-instance 'flow-view)))

(define-application-frame ir1-viewer ()
  ((ir1-flow :reader ir1-flow :initarg :ir1-flow)
   (cur-flow :accessor cur-flow :initform nil))
  (:panes
   (flow :application
	 :display-function #'draw-flow
	 :display-time nil
	 :width *flow-width*
	 :height *flow-height*
	 :end-of-page-action :allow
	 :scroll-bars :both
	 :default-view +flow-view+)
   (info :application
	 :display-time nil
	 :width *flow-width*
	 :default-view +textual-view+)
   (select (make-pane 'option-pane
		      :name "select"
		      :value (setf (cur-flow *application-frame*) (cdar (ir1-flow *application-frame*)))
		      :items (ir1-flow *application-frame*)
		      :name-key (lambda (flow) (label-ir1 (car flow)))
		      :value-key #'cdr
		      :value-changed-callback #'select-flow))
   (quit :push-button
	 :label "Quit"
	 :activate-callback #'exit-viewer))
  (:layouts
   (default
       (horizontally ()
	 (vertically ()
	   select
	   flow)
	 (vertically ()
	   info
	   quit)))))

(defun view (clambda)
  (let ((ir1-flow (make-ir1-flow clambda)))
    (find-application-frame (label-ir1 clambda) :ir1-flow ir1-flow :create t :own-process t :frame-class 'ir1-viewer)))

(defun exit-viewer (&rest args)
  (declare (ignore args))
  (frame-exit *application-frame*))

(defun select-flow (pane value)
  (declare (ignore pane))
  (setf (cur-flow *application-frame*) value)
  (redisplay-frame-pane *application-frame* 'flow :force-p t))

(defun draw-flow (frame stream)
  (window-clear stream)
  (let ((*ir1-flow* (cur-flow frame)))
    (loop for ir1 being each hash-key in *ir1-flow*
       do (progn
	    (present ir1 (presentation-type-of ir1) :stream stream)
	    (draw-ir1-extra ir1 stream)))))

(define-ir1-viewer-command com-describe ((ir1 'ir1))
  (let ((stream (get-frame-pane *application-frame* 'info)))
    (window-clear stream)
    (handler-case (describe ir1 stream)
      (error (e) (notify-user *application-frame* (format nil "~a" e))))))

(define-ir1-viewer-command com-view ((ir1 'sb-c::clambda))
  (setf (gadget-value (find-pane-named *application-frame* 'select) :invoke-callback t)
	(cdr (assoc ir1 (ir1-flow *application-frame*)))))

(labels ((present-instance-slots-clim (thing stream)
           (let ((slots (clim-mop:class-slots (class-of thing))))
             (formatting-table (stream)
               (dolist (slot slots)
                 (formatting-row (stream)
                   (formatting-cell (stream)
                     (present (clim-mop:slot-definition-name slot)
			      'symbol
			      :stream stream))
                   (formatting-cell (stream)
                     (if (slot-boundp thing (clim-mop:slot-definition-name slot))
                         (let ((val (slot-value thing (clim-mop:slot-definition-name slot))))
			   (present val (presentation-type-of val) :stream stream))
                         (format stream "<unbound>"))))))))
         
         (describe-instance (thing a-what stream)  
           (clim:present thing (clim:presentation-type-of thing)
                         :stream stream)
           (format stream " is ~A of type " a-what)
           (clim:present (type-of thing) (clim:presentation-type-of (type-of thing))
                         :stream stream)
           (terpri stream)
           (format stream "It has the following slots:~%")
	   (present-instance-slots-clim thing stream)))
  
  (defmethod describe-object ((thing standard-object) (stream application-pane))
    (describe-instance thing "an instance" stream))
  
  (defmethod describe-object ((thing structure-object) (stream application-pane))
    (describe-instance thing "a structure" stream)))

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

(defstruct (ir1 (:constructor make-ir1 ())) (|bogus-can't-be-instantiated| (error "ir1 is not a concrete ir1 thing.")))

(define-ir1-presentation-type (ir1) ())

(define-ir1-presentation-type (sb-c::cblock
			       sb-c::clambda
			       sb-c::component
			       sb-c::ctran
			       sb-c::lvar
			       sb-c::node
			       sb-c::lexenv) () :inherit-from 'ir1)

(define-ir1-presentation-type (sb-c::bind
			       sb-c::cast
			       sb-c::cif
			       sb-c::combination
			       sb-c::creturn
			       sb-c::entry
			       sb-c::exit
			       sb-c::ref) () :inherit-from 'sb-c::node)

(define-presentation-to-command-translator describe (ir1 com-describe ir1-viewer :gesture :select) (object)
  `(,object))

(define-presentation-to-command-translator view (sb-c::clambda com-view ir1-viewer :gesture nil) (object)
  `(,object))

(defmethod print-object :around ((ctran sb-c::ctran) stream)
  (let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
	( sb-c::*number-continuations* *copy-of-number-continuations*))
    (call-next-method)))

(defmethod print-object :around ((lvar sb-c::lvar) stream)
  (let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
	( sb-c::*number-continuations* *copy-of-number-continuations*))
    (call-next-method)))

(defmethod print-object :around ((cblock sb-c::cblock) stream)
  (let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
	( sb-c::*number-continuations* *copy-of-number-continuations*))
    (call-next-method)))

(define-presentation-method present (ir1 (type ir1) stream view &key acceptably)
  (declare (ignorable acceptably))
  (print ir1))

(define-ir1-presentation-method present (node (type (sb-c::node)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (with-valid-region (region-node node)
    (draw-circle* stream
		  (center-of (min-x it) (max-x it))
		  (center-of (min-y it) (max-y it))
		  (center-of (max-x it) (- (min-x it))))))

(define-ir1-presentation-method present (ctran (type (sb-c::ctran)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (with-valid-region (region-ctran ctran)
    (draw-arrow stream
		(line-start-point it)
		(line-end-point it)
		:ink +red+)
    (draw-text stream (label-ir1 ctran) (line-middle-point it) :align-x :left :align-y :center)))

(define-ir1-presentation-method present (lvar (type (sb-c::lvar)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (let ((uses (previous-of lvar)))
    (with-valid-region (region-lvar lvar)
      (map-over-polyline
       (lambda (x1 y1 x2 y2)
	 (if (/= x1 x2)
	     (progn (draw-arrow* stream x1 y1 x2 y2 :ink +green+)
		    (draw-text* stream (label-ir1 lvar) (center-of x1 x2) (center-of y1 y2) :align-x :left :align-y :center))
	     (let* ((component (sb-c::block-component (sb-c::node-block (first uses)))))
	       (with-valid-region (region-component component)
		 (let* ((component-height (- (max-y it) (min-y it)))
			(lvar-length (sqrt (+ (* (- x2 x1) (- x2 x1)) (* (- y2 y1) (- y2 y1)))))
			(lvar-shift (/ (* 4 *flow-x-spacing* lvar-length) component-height)))
		   (draw-line* stream
			       x1 y1
			       (- x1 lvar-shift) (if (> y1 y2) (- y1 lvar-shift) (+ y1 lvar-shift))
			       :ink +green+)
		   (draw-line* stream
			       (- x1 lvar-shift) (if (> y1 y2) (- y1 lvar-shift) (+ y1 lvar-shift))
			       (- x2 lvar-shift) (if (> y1 y2) (+ y2 lvar-shift) (- y2 lvar-shift))
			       :ink +green+)
		   (draw-text* stream (label-ir1 lvar)
			       (center-of (- x1 lvar-shift) (- x2 lvar-shift))
			       (center-of (if (> y1 y2) (- y1 lvar-shift) (+ y1 lvar-shift)) (if (> y1 y2) (+ y2 lvar-shift) (- y2 lvar-shift)))
			       :align-x :right :align-y :center)
		   (draw-arrow* stream
				(- x2 lvar-shift) (if (> y1 y2) (+ y2 lvar-shift) (- y2 lvar-shift))
				x2 y2 
				:ink +green+))))))
       it))))

(define-ir1-presentation-method present (c (type (sb-c::cblock sb-c::component sb-c::clambda)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (with-valid-region (region-ir1 c)
    (draw-rectangle* stream
		     (min-x it)
		     (min-y it)
		     (max-x it)
		     (max-y it) 
		     :filled nil)
    (draw-text* stream (label-ir1 c) (+ (min-x it) 1) (+ (min-y it) 1) :align-x :left :align-y :top)))

;;; IR1 Extra Drawing
(defgeneric draw-ir1-extra (ir1 &optional stream)
  (:method ((ir1 t) &optional (stream *standard-output*)) (declare (ignore stream)) nil))

(defmethod draw-ir1-extra ((cblock sb-c::cblock) &optional (stream *standard-output*))
  (with-valid-region (region-cblock cblock)
    (let ((pred-it it))
      (dolist (succ (next-of cblock))
	(with-valid-region (region-cblock succ)
	  (draw-arrow* stream
		       (center-of (min-x pred-it) (max-x pred-it))
		       (max-y pred-it)
		       (center-of (min-x it) (max-x it))
		       (min-y it)
		       :ink +blue+))))))

(defmethod draw-ir1-extra ((component sb-c::component) &optional (stream *standard-output*))
  (with-valid-region (region-component component)
    (let ((pred-it it))
      (dolist (succ (next-of (sb-c::component-head component)))
	(with-valid-region (region-cblock succ)
	  (draw-arrow* stream
		       (center-of (min-x pred-it) (max-x pred-it))
		       (min-y pred-it)
		       (center-of (min-x it) (max-x it))
		       (min-y it)
		       :ink +blue+))))))

;;; IR1 Labels
(defgeneric label-ir1 (ir1)
  (:method ((ir1 t)) ""))

(defmethod label-ir1 ((ir1 sb-c::clambda))
  (format nil "~a:~a" (type-of ir1) (sb-c::lambda-%debug-name ir1)))

(defmethod label-ir1 ((ir1 sb-c::component))
  (format nil "~a:~a" (type-of ir1) (sb-c::component-name ir1)))

(defmethod label-ir1 ((ir1 sb-c::cblock))
  (format nil "~a" (type-of ir1)))

(defmethod label-ir1 ((ir1 sb-c::node))
  (format nil "~a:~a" (type-of ir1) (sb-c::node-source-form ir1)))


;;; Top Interface
(define-condition view-ir1 (simple-condition)
  ((clambda :initarg :clambda :reader clambda)))

(defmacro view-ir1 (form-being-compiled)
  (with-unique-names (make-functional-from-toplevel-lambda %simple-eval)
    `(progn
       (eval-when (:compile-toplevel :execute) 
	 (unlock-package (find-package :sb-c))
	 (unlock-package (find-package :sb-impl))
	 
	 (let ((,%simple-eval (symbol-function 'sb-impl::%simple-eval))
	       (,make-functional-from-toplevel-lambda (symbol-function 'sb-c::make-functional-from-toplevel-lambda)))
	   (setf
	    (symbol-function 'sb-impl::%simple-eval)
	    (lambda (expr lexenv)
	      (setf (symbol-function 'sb-impl::%simple-eval) ,%simple-eval)
	      (handler-case (let ((*error-output* (make-string-output-stream))) (funcall ,%simple-eval expr lexenv))
	     	(view-ir1 (clambda) (print-log "ok.") clambda)))
	    
	    (symbol-function 'sb-c::make-functional-from-toplevel-lambda)
	    (lambda (lambda-expression &key name (path (sb-c::missing-arg)))
	      (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) ,make-functional-from-toplevel-lambda)
	      (print-log "compiling ~a~%" lambda-expression)
	      (let ((clambda (funcall ,make-functional-from-toplevel-lambda lambda-expression :name name :path path)))
		(setf *copy-of-continuation-numbers* sb-c::*continuation-numbers*
		      *copy-of-number-continuations* sb-c::*number-continuations*)
		(view clambda)
		(print-log "viewing ~a~%" clambda)
		(signal 'view-ir1 :clambda clambda)
		clambda)))))
       ,form-being-compiled)))