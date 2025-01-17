/**
 * @license Angular v6.1.10
 * (c) 2010-2018 Google, Inc. https://angular.io/
 * License: MIT
 */
var r = (function () {
		return function () {};
	})(),
	i = (function () {
		return function () {};
	})(),
	o = "*";
function a(e, t) {
	return { type: 7, name: e, definitions: t, options: {} };
}
function s(e, t) {
	return void 0 === t && (t = null), { type: 4, styles: t, timings: e };
}
function u(e, t) {
	return void 0 === t && (t = null), { type: 2, steps: e, options: t };
}
function l(e) {
	return { type: 6, styles: e, offset: null };
}
function c(e, t, n) {
	return { type: 0, name: e, styles: t, options: n };
}
function d(e, t, n) {
	return (
		void 0 === n && (n = null),
		{ type: 1, expr: e, animation: t, options: n }
	);
}
/**
 * @license
 * Copyright Google Inc. All Rights Reserved.
 *
 * Use of this source code is governed by an MIT-style license that can be
 * found in the LICENSE file at https://angular.io/license
 */
function p(e) {
	Promise.resolve(null).then(e);
}
/**
 * @license
 * Copyright Google Inc. All Rights Reserved.
 *
 * Use of this source code is governed by an MIT-style license that can be
 * found in the LICENSE file at https://angular.io/license
 */ var f = (function () {
		function e(e, t) {
			void 0 === e && (e = 0),
				void 0 === t && (t = 0),
				(this._onDoneFns = []),
				(this._onStartFns = []),
				(this._onDestroyFns = []),
				(this._started = !1),
				(this._destroyed = !1),
				(this._finished = !1),
				(this.parentPlayer = null),
				(this.totalTime = e + t);
		}
		return (
			(e.prototype._onFinish = function () {
				this._finished ||
					((this._finished = !0),
					this._onDoneFns.forEach(function (e) {
						return e();
					}),
					(this._onDoneFns = []));
			}),
			(e.prototype.onStart = function (e) {
				this._onStartFns.push(e);
			}),
			(e.prototype.onDone = function (e) {
				this._onDoneFns.push(e);
			}),
			(e.prototype.onDestroy = function (e) {
				this._onDestroyFns.push(e);
			}),
			(e.prototype.hasStarted = function () {
				return this._started;
			}),
			(e.prototype.init = function () {}),
			(e.prototype.play = function () {
				this.hasStarted() || (this._onStart(), this.triggerMicrotask()),
					(this._started = !0);
			}),
			(e.prototype.triggerMicrotask = function () {
				var e = this;
				p(function () {
					return e._onFinish();
				});
			}),
			(e.prototype._onStart = function () {
				this._onStartFns.forEach(function (e) {
					return e();
				}),
					(this._onStartFns = []);
			}),
			(e.prototype.pause = function () {}),
			(e.prototype.restart = function () {}),
			(e.prototype.finish = function () {
				this._onFinish();
			}),
			(e.prototype.destroy = function () {
				this._destroyed ||
					((this._destroyed = !0),
					this.hasStarted() || this._onStart(),
					this.finish(),
					this._onDestroyFns.forEach(function (e) {
						return e();
					}),
					(this._onDestroyFns = []));
			}),
			(e.prototype.reset = function () {}),
			(e.prototype.setPosition = function (e) {}),
			(e.prototype.getPosition = function () {
				return 0;
			}),
			(e.prototype.triggerCallback = function (e) {
				var t = "start" == e ? this._onStartFns : this._onDoneFns;
				t.forEach(function (e) {
					return e();
				}),
					(t.length = 0);
			}),
			e
		);
	})(),
	h = (function () {
		function e(e) {
			var t = this;
			(this._onDoneFns = []),
				(this._onStartFns = []),
				(this._finished = !1),
				(this._started = !1),
				(this._destroyed = !1),
				(this._onDestroyFns = []),
				(this.parentPlayer = null),
				(this.totalTime = 0),
				(this.players = e);
			var n = 0,
				r = 0,
				i = 0,
				o = this.players.length;
			0 == o
				? p(function () {
						return t._onFinish();
					})
				: this.players.forEach(function (e) {
						e.onDone(function () {
							++n == o && t._onFinish();
						}),
							e.onDestroy(function () {
								++r == o && t._onDestroy();
							}),
							e.onStart(function () {
								++i == o && t._onStart();
							});
					}),
				(this.totalTime = this.players.reduce(function (e, t) {
					return Math.max(e, t.totalTime);
				}, 0));
		}
		return (
			(e.prototype._onFinish = function () {
				this._finished ||
					((this._finished = !0),
					this._onDoneFns.forEach(function (e) {
						return e();
					}),
					(this._onDoneFns = []));
			}),
			(e.prototype.init = function () {
				this.players.forEach(function (e) {
					return e.init();
				});
			}),
			(e.prototype.onStart = function (e) {
				this._onStartFns.push(e);
			}),
			(e.prototype._onStart = function () {
				this.hasStarted() ||
					((this._started = !0),
					this._onStartFns.forEach(function (e) {
						return e();
					}),
					(this._onStartFns = []));
			}),
			(e.prototype.onDone = function (e) {
				this._onDoneFns.push(e);
			}),
			(e.prototype.onDestroy = function (e) {
				this._onDestroyFns.push(e);
			}),
			(e.prototype.hasStarted = function () {
				return this._started;
			}),
			(e.prototype.play = function () {
				this.parentPlayer || this.init(),
					this._onStart(),
					this.players.forEach(function (e) {
						return e.play();
					});
			}),
			(e.prototype.pause = function () {
				this.players.forEach(function (e) {
					return e.pause();
				});
			}),
			(e.prototype.restart = function () {
				this.players.forEach(function (e) {
					return e.restart();
				});
			}),
			(e.prototype.finish = function () {
				this._onFinish(),
					this.players.forEach(function (e) {
						return e.finish();
					});
			}),
			(e.prototype.destroy = function () {
				this._onDestroy();
			}),
			(e.prototype._onDestroy = function () {
				this._destroyed ||
					((this._destroyed = !0),
					this._onFinish(),
					this.players.forEach(function (e) {
						return e.destroy();
					}),
					this._onDestroyFns.forEach(function (e) {
						return e();
					}),
					(this._onDestroyFns = []));
			}),
			(e.prototype.reset = function () {
				this.players.forEach(function (e) {
					return e.reset();
				}),
					(this._destroyed = !1),
					(this._finished = !1),
					(this._started = !1);
			}),
			(e.prototype.setPosition = function (e) {
				var t = e * this.totalTime;
				this.players.forEach(function (e) {
					var n = e.totalTime ? Math.min(1, t / e.totalTime) : 1;
					e.setPosition(n);
				});
			}),
			(e.prototype.getPosition = function () {
				var e = 0;
				return (
					this.players.forEach(function (t) {
						var n = t.getPosition();
						e = Math.min(n, e);
					}),
					e
				);
			}),
			(e.prototype.beforeDestroy = function () {
				this.players.forEach(function (e) {
					e.beforeDestroy && e.beforeDestroy();
				});
			}),
			(e.prototype.triggerCallback = function (e) {
				var t = "start" == e ? this._onStartFns : this._onDoneFns;
				t.forEach(function (e) {
					return e();
				}),
					(t.length = 0);
			}),
			e
		);
	})(),
	m = "!";
    /**
     * @license Angular v6.1.10
     * (c) 2010-2018 Google, Inc. https://angular.io/
     * License: MIT
     */
    var r=function(){return function(){}}(),i=function(){return function(){}}(),o="*";function a(e,t){return{type:7,name:e,definitions:t,options:{}}}function s(e,t){return void 0===t&&(t=null),{type:4,styles:t,timings:e}}function u(e,t){return void 0===t&&(t=null),{type:2,steps:e,options:t}}function l(e){return{type:6,styles:e,offset:null}}function c(e,t,n){return{type:0,name:e,styles:t,options:n}}function d(e,t,n){return void 0===n&&(n=null),{type:1,expr:e,animation:t,options:n}}
    /**
     * @license
     * Copyright Google Inc. All Rights Reserved.
     *
     * Use of this source code is governed by an MIT-style license that can be
     * found in the LICENSE file at https://angular.io/license
     */
    function p(e){Promise.resolve(null).then(e)}
    /**
     * @license
     * Copyright Google Inc. All Rights Reserved.
     *
     * Use of this source code is governed by an MIT-style license that can be
     * found in the LICENSE file at https://angular.io/license
     */var f=function(){function e(e,t){void 0===e&&(e=0),void 0===t&&(t=0),this._onDoneFns=[],this._onStartFns=[],this._onDestroyFns=[],this._started=!1,this._destroyed=!1,this._finished=!1,this.parentPlayer=null,this.totalTime=e+t}return e.prototype._onFinish=function(){this._finished||(this._finished=!0,this._onDoneFns.forEach(function(e){return e()}),this._onDoneFns=[])},e.prototype.onStart=function(e){this._onStartFns.push(e)},e.prototype.onDone=function(e){this._onDoneFns.push(e)},e.prototype.onDestroy=function(e){this._onDestroyFns.push(e)},e.prototype.hasStarted=function(){return this._started},e.prototype.init=function(){},e.prototype.play=function(){this.hasStarted()||(this._onStart(),this.triggerMicrotask()),this._started=!0},e.prototype.triggerMicrotask=function(){var e=this;p(function(){return e._onFinish()})},e.prototype._onStart=function(){this._onStartFns.forEach(function(e){return e()}),this._onStartFns=[]},e.prototype.pause=function(){},e.prototype.restart=function(){},e.prototype.finish=function(){this._onFinish()},e.prototype.destroy=function(){this._destroyed||(this._destroyed=!0,this.hasStarted()||this._onStart(),this.finish(),this._onDestroyFns.forEach(function(e){return e()}),this._onDestroyFns=[])},e.prototype.reset=function(){},e.prototype.setPosition=function(e){},e.prototype.getPosition=function(){return 0},e.prototype.triggerCallback=function(e){var t="start"==e?this._onStartFns:this._onDoneFns;t.forEach(function(e){return e()}),t.length=0},e}(),h=function(){function e(e){var t=this;this._onDoneFns=[],this._onStartFns=[],this._finished=!1,this._started=!1,this._destroyed=!1,this._onDestroyFns=[],this.parentPlayer=null,this.totalTime=0,this.players=e;var n=0,r=0,i=0,o=this.players.length;0==o?p(function(){return t._onFinish()}):this.players.forEach(function(e){e.onDone(function(){++n==o&&t._onFinish()}),e.onDestroy(function(){++r==o&&t._onDestroy()}),e.onStart(function(){++i==o&&t._onStart()})}),this.totalTime=this.players.reduce(function(e,t){return Math.max(e,t.totalTime)},0)}return e.prototype._onFinish=function(){this._finished||(this._finished=!0,this._onDoneFns.forEach(function(e){return e()}),this._onDoneFns=[])},e.prototype.init=function(){this.players.forEach(function(e){return e.init()})},e.prototype.onStart=function(e){this._onStartFns.push(e)},e.prototype._onStart=function(){this.hasStarted()||(this._started=!0,this._onStartFns.forEach(function(e){return e()}),this._onStartFns=[])},e.prototype.onDone=function(e){this._onDoneFns.push(e)},e.prototype.onDestroy=function(e){this._onDestroyFns.push(e)},e.prototype.hasStarted=function(){return this._started},e.prototype.play=function(){this.parentPlayer||this.init(),this._onStart(),this.players.forEach(function(e){return e.play()})},e.prototype.pause=function(){this.players.forEach(function(e){return e.pause()})},e.prototype.restart=function(){this.players.forEach(function(e){return e.restart()})},e.prototype.finish=function(){this._onFinish(),this.players.forEach(function(e){return e.finish()})},e.prototype.destroy=function(){this._onDestroy()},e.prototype._onDestroy=function(){this._destroyed||(this._destroyed=!0,this._onFinish(),this.players.forEach(function(e){return e.destroy()}),this._onDestroyFns.forEach(function(e){return e()}),this._onDestroyFns=[])},e.prototype.reset=function(){this.players.forEach(function(e){return e.reset()}),this._destroyed=!1,this._finished=!1,this._started=!1},e.prototype.setPosition=function(e){var t=e*this.totalTime;this.players.forEach(function(e){var n=e.totalTime?Math.min(1,t/e.totalTime):1;e.setPosition(n)})},e.prototype.getPosition=function(){var e=0;return this.players.forEach(function(t){var n=t.getPosition();e=Math.min(n,e)}),e},e.prototype.beforeDestroy=function(){this.players.forEach(function(e){e.beforeDestroy&&e.beforeDestroy()})},e.prototype.triggerCallback=function(e){var t="start"==e?this._onStartFns:this._onDoneFns;t.forEach(function(e){return e()}),t.length=0},e}(),m="!";
     */var f=function(){function e(e,t){void 0===e&&(e=0),void 0===t&&(t=0),this._onDoneFns=[],this._onStartFns=[],this._onDestroyFns=[],this._started=!1,this._destroyed=!1,this._finished=!1,this.parentPlayer=null,this.totalTime=e+t}return e.prototype._onFinish=function(){this._finished||(this._finished=!0,this._onDoneFns.forEach(function(e){return e()}),this._onDoneFns=[])},e.prototype.onStart=function(e){this._onStartFns.push(e)},e.prototype.onDone=function(e){this._onDoneFns.push(e)},e.prototype.onDestroy=function(e){this._onDestroyFns.push(e)},e.prototype.hasStarted=function(){return this._started},e.prototype.init=function(){},e.prototype.play=function(){this.hasStarted()||(this._onStart(),this.triggerMicrotask()),this._started=!0},e.prototype.triggerMicrotask=function(){var e=this;p(function(){return e._onFinish()})},e.prototype._onStart=function(){this._onStartFns.forEach(function(e){return e()}),this._onStartFns=[]},e.prototype.pause=function(){},e.prototype.restart=function(){},e.prototype.finish=function(){this._onFinish()},e.prototype.destroy=function(){this._destroyed||(this._destroyed=!0,this.hasStarted()||this._onStart(),this.finish(),this._onDestroyFns.forEach(function(e){return e()}),this._onDestroyFns=[])},e.prototype.reset=function(){},e.prototype.setPosition=function(e){},e.prototype.getPosition=function(){return 0},e.prototype.triggerCallback=function(e){var t="start"==e?this._onStartFns:this._onDoneFns;t.forEach(function(e){return e()}),t.length=0},e}(),h=function(){function e(e){var t=this;this._onDoneFns=[],this._onStartFns=[],this._finished=!1,this._started=!1,this._destroyed=!1,this._onDestroyFns=[],this.parentPlayer=null,this.totalTime=0,this.players=e;var n=0,r=0,i=0,o=this.players.length;0==o?p(function(){return t._onFinish()}):this.players.forEach(function(e){e.onDone(function(){++n==o&&t._onFinish()}),e.onDestroy(function(){++r==o&&t._onDestroy()}),e.onStart(function(){++i==o&&t._onStart()})}),this.totalTime=this.players.reduce(function(e,t){return Math.max(e,t.totalTime)},0)}return e.prototype._onFinish=function(){this._finished||(this._finished=!0,this._onDoneFns.forEach(function(e){return e()}),this._onDoneFns=[])},e.prototype.init=function(){this.players.forEach(function(e){return e.init()})},e.prototype.onStart=function(e){this._onStartFns.push(e)},e.prototype._onStart=function(){this.hasStarted()||(this._started=!0,this._onStartFns.forEach(function(e){return e()}),this._onStartFns=[])},e.prototype.onDone=function(e){this._onDoneFns.push(e)},e.prototype.onDestroy=function(e){this._onDestroyFns.push(e)},e.prototype.hasStarted=function(){return this._started},e.prototype.play=function(){this.parentPlayer||this.init(),this._onStart(),this.players.forEach(function(e){return e.play()})},e.prototype.pause=function(){this.players.forEach(function(e){return e.pause()})},e.prototype.restart=function(){this.players.forEach(function(e){return e.restart()})},e.prototype.finish=function(){this._onFinish(),this.players.forEach(function(e){return e.finish()})},e.prototype.destroy=function(){this._onDestroy()},e.prototype._onDestroy=function(){this._destroyed||(this._destroyed=!0,this._onFinish(),this.players.forEach(function(e){return e.destroy()}),this._onDestroyFns.forEach(function(e){return e()}),this._onDestroyFns=[])},e.prototype.reset=function(){this.players.forEach(function(e){return e.reset()}),this._destroyed=!1,this._finished=!1,this._started=!1},e.prototype.setPosition=function(e){var t=e*this.totalTime;this.players.forEach(function(e){var n=e.totalTime?Math.min(1,t/e.totalTime):1;e.setPosition(n)})},e.prototype.getPosition=function(){var e=0;return this.players.forEach(function(t){var n=t.getPosition();e=Math.min(n,e)}),e},e.prototype.beforeDestroy=function(){this.players.forEach(function(e){e.beforeDestroy&&e.beforeDestroy()})},e.prototype.triggerCallback=function(e){var t="start"==e?this._onStartFns:this._onDoneFns;t.forEach(function(e){return e()}),t.length=0},e}(),m="!";