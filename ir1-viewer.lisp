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

(defvar *flow-unit* (/ *screen-width* 40))

(defvar *flow-x-spacing* *flow-unit*)
(defvar *flow-y-spacing* *flow-unit*)
(defvar *flow-block-x-spacing* (* 2 *flow-x-spacing*))
(defvar *flow-block-y-spacing* *flow-y-spacing*)

(defvar *flow-lvar-x-spacing-ratio* 3)

(defvar *flow-margin-ratio-x* 1)
(defvar *flow-margin-ratio-y* 1)
(defvar *flow-clambda-margin-ratio-x* 1/3)
(defvar *flow-clambda-margin-ratio-y* 1/3)
(defvar *flow-block-margin-ratio-x* 2)
(defvar *flow-block-margin-ratio-y* 0)

(defvar *copy-of-continuation-numbers* nil)
(defvar *copy-of-number-continuations* nil)

(defparameter *flow-current-x* 0)
(defparameter *flow-current-y* 0)

(defparameter *flow-current-scaling* 1)

(defparameter *flow-print-lines* 1)
(defparameter *flow-print-level* 2)
(defparameter *flow-print-length* 3)

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

(defun draw-text-in-bounding-rectangle* (stream text bound location &rest args)
  (let ((old-size (getf args :text-size 256))
	(record (with-output-to-output-record (stream) (apply #'draw-text* stream text
							      (case location
								((:bottomleft :topleft) (1+ (min-x bound)))
								((:bottomright :topright) (1- (max-x bound)))
								(t (center-of (min-x bound) (max-x bound))))
							      (case location
								((:topright :topleft) (1+ (min-y bound)))
								((:bottomright :bottomleft) (1- (max-y bound)))
								(t (center-of (min-y bound) (max-y bound)))) args))))
    (when (or (< (bounding-rectangle-width (bounding-rectangle record)) (* *flow-current-scaling* (bounding-rectangle-width bound)))
	      (< old-size 4))
      (apply #'draw-text* stream text
	     (case location
	       ((:bottomleft :topleft) (1+ (min-x bound)))
	       ((:bottomright :topright) (1- (max-x bound)))
	       (t (center-of (min-x bound) (max-x bound))))
	     (case location
	       ((:topright :topleft) (1+ (min-y bound)))
	       ((:bottomright :bottomleft) (1- (max-y bound)))
	       (t (center-of (min-y bound) (max-y bound)))) args)

      (return-from draw-text-in-bounding-rectangle* nil))
    (setf (getf args :text-size) (ceiling (- old-size 1)))
    (apply #'draw-text-in-bounding-rectangle* stream text bound location args)))

(defmacro size-of ((stream) &body body)
  `(let ((record (with-output-to-output-record (,stream)
		   ,@body)))
     (bounding-rectangle-size record)))

(defun component-clambdas (component)
  (remove-duplicates
   (append (sb-c::component-new-functionals component)
	   (sb-c::component-lambdas component)
	   (sb-c::component-reanalyze-functionals component))))

;;; IR1 Regions
(defvar *recompute-p* nil)
(defvar *ir1-flow* nil)

(defun make-ir1-flow (clambda)
  (let ((component (sb-c::lambda-component clambda))
	(*flow-current-x* *flow-current-x*)
	(*flow-current-y* *flow-current-y*)
	(*ir1-flow* (make-hash-table)))
    (region-ir1 component)
    (cons component *ir1-flow*)))

(defun valid-region-p (region)
  (and region (not (eq region +nowhere+)) region))

(defmacro with-valid-region (region &body body)
  `(awhen (valid-region-p ,region)
     ,@body))

(defun margined-region (region &key (x-ratio *flow-margin-ratio-x*) (y-ratio *flow-margin-ratio-y*))
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
    (sb-c::functional (region-functional ir1))
    (sb-c::component (region-component ir1))
    (sb-c::cblock (region-cblock ir1))
    (sb-c::ctran (region-ctran ir1))
    (sb-c::lvar (region-lvar ir1))
    (sb-c::node (region-node ir1))
    (t +nowhere+)))

(define-ir1-region (component)
  (let ((flow-original-x *flow-current-x*))
    (labels ((region-dangling-next-cblocks (cblock-head region)
	       (or (and (sb-c::block-next cblock-head)
			(null (sb-c::block-pred (sb-c::block-next cblock-head)))
			(region-union (region-cblock (sb-c::block-next cblock-head))
				      (region-dangling-next-cblocks (sb-c::block-next cblock-head) region)))
		   (region-cblocks cblock-head region)))
	     (region-cblocks (cblock-head region)
	       (let ((*flow-current-x* *flow-current-x*))
		 (do* ((cblocks (next-of cblock-head) (rest cblocks))
		       (cblock (first cblocks) (first cblocks)))
		      ((null cblocks) (values region *flow-current-x* *flow-current-y*))
		   (let* ((*flow-current-y* *flow-current-y*)
			  (cblock-region (region-cblock cblock))
			  (cblock-next-region (region-dangling-next-cblocks cblock region))
					;(cblock-succ-region (region-cblocks cblock region))
			  )
		     (setf region (reduce #'region-union (list cblock-region ;; cblock-succ-region
							       cblock-next-region)))
		     (when (valid-region-p region)
		       (setf *flow-current-x* (+ flow-original-x
						 (bounding-rectangle-width region)
						 *flow-block-x-spacing*)))))))
	     (region-lvars (cblock-head)
	       (do ((cblocks (next-of cblock-head) (rest cblocks)))
		   ((null cblocks))
		 (do* ((ctran (sb-c::block-start (first cblocks)) (next-of node))
		       (node (next-of ctran) (next-of ctran))
		       (lvar (and (sb-c::valued-node-p node) (sb-c::node-lvar node)) (and (sb-c::valued-node-p node) (sb-c::node-lvar node))))
		      ((null ctran))
		   (region-lvar lvar))
		 (region-lvars (first cblocks))))
	     (region-functionals ()
	       (multiple-value-bind (br cx cy) (region-cblocks (sb-c::component-head component) +nowhere+)
		 (declare (ignore br))
		 (let ((*flow-current-x* cx)
		       (*flow-current-y* cy))
		   (reduce #'region-union
			   (mapcar #'region-functional
				   (component-clambdas component))
			   :initial-value +nowhere+)))))
      (prog1 (margined-region (region-functionals))
	(region-lvars (sb-c::component-head component))))))

(define-ir1-region (functional)
  (typecase functional
    (sb-c::clambda (do* ((cblock (sb-c::lambda-block functional) (sb-c::block-next cblock))
			 (region (region-cblock cblock) (region-union region (region-cblock cblock))))
			((eq cblock (sb-c::node-block (sb-c::lambda-return functional)))
			 (margined-region (region-union region 
							(reduce #'region-union (mapcar #'region-functional (sb-c::lambda-children functional)) :initial-value +nowhere+))
					  :x-ratio *flow-clambda-margin-ratio-x*
					  :y-ratio *flow-clambda-margin-ratio-y*))))
    (sb-c::optional-dispatch
     (margined-region
      (reduce #'region-union
	      (remove-duplicates
	       (mapcar #'region-functional
		       (list*
			(sb-c::optional-dispatch-main-entry functional)
			(sb-c::optional-dispatch-more-entry functional)
			(remove-if-not #'sb-c::functional-p
				       (sb-c::optional-dispatch-entry-points functional)))))
	      :initial-value +nowhere+)
      :x-ratio *flow-clambda-margin-ratio-x*
      :y-ratio *flow-clambda-margin-ratio-y*))))

(define-ir1-region (cblock)
  (do* ((region +nowhere+ (region-union region (region-union (region-node node) (bounding-rectangle (region-ctran ctran)))))
	(ctran (sb-c::block-start cblock) (next-of node))
	(node (next-of ctran) (next-of ctran)))
       ((null ctran) (margined-region region :x-ratio *flow-block-margin-ratio-x* :y-ratio *flow-block-margin-ratio-y*))))

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
      (setf *flow-current-y* (+ *flow-current-y* *flow-block-y-spacing*)))))

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
    (sb-c::cblock (if (equal (sb-c::block-succ ir1) (sb-c::block-pred ir1))
		      (list (sb-c::block-next ir1))
		      (sb-c::block-succ ir1)))
    (t nil)))

;;; Clim
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass flow-view (gadget-view) ())
  (defparameter +flow-view+ (make-instance 'flow-view)))

(define-application-frame ir1-viewer ()
  ((ir1-flow :reader ir1-flow :initarg :ir1-flow))
  (:pointer-documentation t)
  (:panes
   (flow :application
	 :display-function #'draw-flow-pane
	 :display-time nil
	 :end-of-page-action :allow
	 :scroll-bars :both
	 :default-view +flow-view+)
   (info :application
	 :display-time nil
	 :scroll-bars :both
	 :default-view +textual-view+))
  (:layouts
   (default
       (horizontally ()
	 (2/3 flow)
	 (1/3 info)))
   (only-flow
    flow)))

(defun run-viewer (clambda)
  (let ((ir1-flow (make-ir1-flow clambda)))
    (find-application-frame 'ir1-viewer :ir1-flow ir1-flow :create t :own-process t :frame-class 'ir1-viewer)))

(defun draw-flow-pane (frame stream)
  (draw-flow (ir1-flow frame) stream))

(defun draw-flow (ir1-flow stream &key (view +flow-view+))
  (window-clear stream)
  (let ((component-region (region-component (car ir1-flow))))
    (with-scaling (stream *flow-current-scaling*)
      (with-translation (stream (- (min-x component-region)) (- (min-y component-region)))
	(with-drawing-options (stream)
	  (loop for ir1 being each hash-key in (cdr ir1-flow)
	     do (progn
		  (draw-ir1-extra ir1 stream)
		  (present ir1 (presentation-type-of ir1) :stream stream :view view))))))))

(define-ir1-viewer-command com-describe ((ir1 'ir1))
  (when (eq (frame-current-layout *application-frame*) 'default)
    (let ((stream (get-frame-pane *application-frame* 'info)))
      (window-clear stream)
      (handler-case (describe ir1 stream)
	(error (e) (notify-user *application-frame* (format nil "~a" e)))))))

(define-ir1-viewer-command (com-zoom-in :menu t :keystroke (:z :shift)) ()
  (setf *flow-current-scaling* (* 2 *flow-current-scaling*))
  (redisplay-frame-pane *application-frame* 'flow :force-p t))

(define-ir1-viewer-command (com-zoom-out :menu t :keystroke :z) ()
  (setf *flow-current-scaling* (/ *flow-current-scaling* 2))
  (redisplay-frame-pane *application-frame* 'flow :force-p t))

(define-ir1-viewer-command (com-toggle-info :menu t :keystroke :f) ()
  (if (eq (frame-current-layout *application-frame*) 'default)
      (setf (frame-current-layout *application-frame*) 'only-flow)
      (setf (frame-current-layout *application-frame*) 'default)))

(define-ir1-viewer-command (com-quit :menu t :keystroke :q) ()
  (frame-exit *application-frame*))

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
			       sb-c::functional
			       sb-c::component
			       sb-c::ctran
			       sb-c::lvar
			       sb-c::node
			       sb-c::lexenv) () :inherit-from 'ir1)

(define-ir1-presentation-type (sb-c::bind
			       sb-c::cast
			       sb-c::cif
			       sb-c::creturn
			       sb-c::entry
			       sb-c::exit
			       sb-c::ref
			       sb-c::basic-combination) () :inherit-from 'sb-c::node)

(define-ir1-presentation-type (sb-c::combination
			       sb-c::mv-combination) () :inherit-from 'sb-c::basic-combination)

(define-ir1-presentation-type (sb-c::clambda
			       sb-c::optional-dispatch) () :inherit-from 'sb-c::functional)

(define-presentation-to-command-translator describe (ir1 com-describe ir1-viewer :gesture :select) (object)
  `(,object))

(macrolet ((def (ir1)
	     `(defmethod print-object :around ((ctran ,ir1) stream)
		(let ((sb-c::*continuation-numbers* *copy-of-continuation-numbers*)
		      ( sb-c::*number-continuations* *copy-of-number-continuations*))
		  (call-next-method)))))
  (def sb-c::ctran)
  (def sb-c::lvar)
  (def sb-c::cblock))

(define-presentation-method present (ir1 (type ir1) stream view &key acceptably)
  (declare (ignorable acceptably))
  (print ir1))

(define-ir1-presentation-method present (node (type (sb-c::node)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (with-valid-region (region-node node)
    (draw-circle* stream
		  (center-of (min-x it) (max-x it))
		  (center-of (min-y it) (max-y it))
		  (center-of (max-y it) (- (min-y it)))
		  :filled nil)
    (let* ((rb (region-cblock (sb-c::node-block node)))
	   (nb (make-bounding-rectangle (min-x rb) (min-y it) (max-x rb) (max-y it))))
      (draw-text-in-bounding-rectangle* stream (label-ir1 node) nb :center :align-x :center :align-y :center))))

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
			(lvar-shift (/ (* *flow-lvar-x-spacing-ratio* *flow-x-spacing* lvar-length) component-height)))
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

(define-ir1-presentation-method present (c (type (sb-c::cblock sb-c::component sb-c::functional)) stream (view (eql +flow-view+)) &key acceptably)
  (declare (ignorable acceptably))
  (with-valid-region (region-ir1 c)
    (draw-rectangle* stream
		     (min-x it)
		     (min-y it)
		     (max-x it)
		     (max-y it)
		     :filled nil)
    (draw-text-in-bounding-rectangle* stream (label-ir1 c) it :topleft :align-x :left :align-y :top)))

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
  (:method ((ir1 t)) "")
  (:method :around ((ir1 t))
	   (let ((*print-lines* *flow-print-lines*)
		 (*print-level* *flow-print-level*)
		 (*print-length* *flow-print-length*))
	     (call-next-method))))

(defmethod label-ir1 ((ir1 sb-c::functional))
  (format nil "~a:~a" (type-of ir1) (or (sb-c::functional-%debug-name ir1) (sb-c::functional-%source-name ir1))))

(defmethod label-ir1 ((ir1 sb-c::component))
  (format nil "~a:~a" (type-of ir1) (sb-c::component-name ir1)))

(defmethod label-ir1 ((ir1 sb-c::cblock))
  (format nil "~a" (type-of ir1)))

(defmethod label-ir1 ((ir1 sb-c::node))
  (handler-case (let ((form (sb-c::node-source-form ir1)))
		  (format nil "~a:~a" (type-of ir1)
			  (if (sb-c::leaf-p form)
			      (or (sb-c::leaf-%debug-name form) (sb-c::leaf-%source-name form))
			      form)))
    (error () (format nil "~a" (type-of ir1)))))

;;; Top Interface

;;; Clim GUI
(define-condition view-ir1 (simple-condition)
  ((clambda :initarg :clambda :reader clambda)))

(defmacro view (form-being-compiled)
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
	      (handler-case (let ((*error-output* (make-string-output-stream)))
			      (funcall ,%simple-eval expr lexenv))
		(condition () (print-log "returning~%")
			   ,(cond
			     ((eq (car form-being-compiled) 'defun)
			      `(symbol-function (compile ',(cadr form-being-compiled) (lambda ,(caddr form-being-compiled) ,@(cdddr form-being-compiled)))))
			     ((eq (car form-being-compiled) 'lambda)
			      `(compile nil ,form-being-compiled))
			     ((eq (car form-being-compiled) 'eval-when)
			      `(compile nil (lambda () ,@(cddr form-being-compiled))))
			     (t
			      `(compile nil (lambda () ,form-being-compiled)))))))
	    
	    (symbol-function 'sb-c::make-functional-from-toplevel-lambda)
	    (lambda (lambda-expression &key name (path (sb-c::missing-arg)))
	      (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) ,make-functional-from-toplevel-lambda)
	      (print-log "compiling ~a~%" lambda-expression)
	      (let ((clambda (funcall ,make-functional-from-toplevel-lambda lambda-expression :name name :path path)))
		(setf *copy-of-continuation-numbers* sb-c::*continuation-numbers*
		      *copy-of-number-continuations* sb-c::*number-continuations*)
		(print-log "viewing ~a~%" clambda)
		(run-viewer clambda)
		
		(signal 'view-ir1 :clambda clambda)
		clambda)))))
       ,(cond ((member (car form-being-compiled) '(defun lambda named-lambda))
	       form-being-compiled)
	      ((eq (car form-being-compiled) 'eval-when)
	       `(lambda () ,@(cddr form-being-compiled)))
	      (t
	       `(lambda () ,form-being-compiled))))))

;;; Dump PS file
(defmethod window-clear (pane) nil)

(defmacro dump (body &key (to-dir "~/"))
  (with-unique-names (make-functional-from-toplevel-lambda fmake-functional-from-toplevel-lambda)
    `(progn
       (unlock-package (find-package :sb-c))
       (defparameter ,make-functional-from-toplevel-lambda (symbol-function 'sb-c::make-functional-from-toplevel-lambda))
       (defun ,fmake-functional-from-toplevel-lambda (lambda-expression &key name (path (sb-c::missing-arg)))
	 (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) ,make-functional-from-toplevel-lambda)
	 (print-log "compiling ~a~%" lambda-expression)
	 (let* ((clambda (funcall ,make-functional-from-toplevel-lambda lambda-expression :name name :path path))
		(ps (merge-pathnames (pathname (format nil "~a-~a.ps" 
						    (sb-c::component-name (sb-c::lambda-component clambda))
						    (sb-kernel::get-lisp-obj-address (sb-c::lambda-component clambda))))
				  ,to-dir)))
	   (print-log "dumping ~a to ~a ~%" clambda ps)
	   (progn (with-open-file (f ps :direction :output :if-exists :supersede :if-does-not-exist :create)
		    (let ((*flow-print-level* nil)
			  (*flow-print-length* nil))
		     (with-output-to-postscript-stream (s f :device-type :eps)
		       (draw-flow (make-ir1-flow clambda) s)))))
	   (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) #',fmake-functional-from-toplevel-lambda)
	   (print-log "returning ~%")
	   clambda))
       ((lambda ()
	  (unwind-protect
	       (progn
		 (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) #',fmake-functional-from-toplevel-lambda)
		 (eval ',body)
		 (setf (symbol-function 'sb-c::make-functional-from-toplevel-lambda) ,make-functional-from-toplevel-lambda))))))))