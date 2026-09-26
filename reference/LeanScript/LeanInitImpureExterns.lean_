module
prelude
public import LeanScript.LeanPrimTy
public import LeanScript.LeanPrimTyCovariant
public import Init.Data.FloatArray.Basic
public import Init.System.IO
public import Init.System.Promise
public import Init.ShareCommon
set_option autoImplicit false
@[expose] public section
namespace LeanScript

open LeanPrimTy
open LeanPrimTyCovariant

protected abbrev LeanPrimTy.usize : LeanPrimTy := uint64
protected abbrev LeanPrimTy.isize : LeanPrimTy := int64

variable {MyTy : Type}
  (denote : MyTy → Type)
  [Coe LeanPrimTy MyTy]
  [Coe (LeanPrimTyCovariant LeanPrimTy) MyTy]
  [Coe (LeanPrimTyCovariant MyTy) MyTy]
  (option : MyTy → MyTy)
  (list : MyTy → MyTy)
  (fn1 : MyTy → MyTy → MyTy)
  (fn2 : MyTy → MyTy → MyTy → MyTy)
  (prod : MyTy → MyTy → MyTy)
  (name : MyTy)
  (ordering : MyTy)
  (byteArray : MyTy)
  (floatArray : MyTy)
  (stRef : MyTy → MyTy → MyTy)
  (unit : MyTy)
  (void : MyTy → MyTy)
  (baseIO : MyTy → MyTy)
  (io_taskState : MyTy)
  (io_fs_stream : MyTy)
  (system_filePath : MyTy)
  (io_fs_metadata : MyTy)
  (io_fs_dirEntry : MyTy)
  (io_fs_handle : MyTy)
  (io : MyTy -> MyTy)
  (io_promise : MyTy -> MyTy)
  (io_process_child : IO.Process.StdioConfig -> MyTy)
  (io_process_stdio_toHandleType : IO.Process.Stdio -> MyTy)

inductive LeanInitImpureExtern : MyTy → Type where
  ----------------------
  -- Init/System/ST.lean
  ----------------------
  | lean_st_mk_ref : (σt : MyTy) → (αt : MyTy) → denote αt → LeanInitImpureExtern (stRef σt αt) -- ST.Prim.mkRef
  | lean_st_ref_ptr_eq : (σt : MyTy) → (αt : MyTy) → denote (stRef σt αt) → denote (stRef σt αt) → LeanInitImpureExtern LeanPrimTy.bool -- ST.Prim.Ref.ptrEq
  | lean_st_ref_get : (σt : MyTy) → (αt : MyTy) → denote (stRef σt αt) → LeanInitImpureExtern αt -- ST.Prim.Ref.get
  | lean_st_ref_swap : (σt : MyTy) → (αt : MyTy) → denote (stRef σt αt) → denote αt → LeanInitImpureExtern αt -- ST.Prim.Ref.swap
  | lean_st_ref_take : (σt : MyTy) → (αt : MyTy) → denote (stRef σt αt) → LeanInitImpureExtern αt -- ST.Prim.Ref.take
  | lean_st_ref_put : (σt : MyTy) → (αt : MyTy) → denote (stRef σt αt) → denote αt → LeanInitImpureExtern unit -- ST.Prim.Ref.put
  | lean_void_mk : (σt : MyTy) → denote σt → LeanInitImpureExtern (void σt) -- Void.mk
  ----------------------
  -- Init/System/IO.lean
  ----------------------
  | lean_io_map_task : (αt : MyTy) → (βt : MyTy) → (denote αt → denote (baseIO βt)) → denote (task αt) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → LeanInitImpureExtern (task βt) -- BaseIO.mapTask
  | lean_io_prim_handle_rewind : denote io_fs_handle → LeanInitImpureExtern unit -- io_fs_handle.rewind
  | lean_io_process_child_wait : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitImpureExtern uint32 -- IO.Process.Child.wait
  | lean_get_set_stderr : denote io_fs_stream → LeanInitImpureExtern io_fs_stream -- IO.setStderr
  | lean_io_prim_handle_is_tty : denote io_fs_handle → LeanInitImpureExtern LeanPrimTy.bool -- io_fs_handle.isTty
  | lean_io_rename : denote system_filePath → denote system_filePath → LeanInitImpureExtern unit -- IO.FS.rename
  | lean_io_process_set_current_dir : denote system_filePath → LeanInitImpureExtern unit -- IO.Process.setCurrentDir
  | lean_io_get_num_heartbeats : LeanInitImpureExtern nat -- IO.getNumHeartbeats
  | lean_io_cancel : (αt : MyTy) → denote (task αt) → LeanInitImpureExtern unit -- IO.cancel
  | lean_io_allocprof : (αt : MyTy) → String → denote (io αt) → LeanInitImpureExtern αt -- allocprof
  | lean_io_read_dir : denote system_filePath → LeanInitImpureExtern (array io_fs_dirEntry) -- System.FilePath.readDir
  | lean_io_force_exit : (αt : MyTy) → UInt8 → LeanInitImpureExtern αt -- IO.Process.forceExit
  | lean_io_prim_handle_mk : denote system_filePath → IO.FS.Mode → LeanInitImpureExtern io_fs_handle -- io_fs_handle.mk
  | lean_io_wait_any : (αt : MyTy) → (tasks : List (denote (task αt))) → (h : tasks.length > 0 := by exact Nat.zero_lt_succ _) → LeanInitImpureExtern αt -- IO.waitAny
  | lean_io_prim_handle_read : denote io_fs_handle → denote LeanPrimTy.usize → LeanInitImpureExtern byteArray -- io_fs_handle.read
  | lean_io_getenv : String → LeanInitImpureExtern (option string) -- IO.getEnv
  | lean_io_prim_handle_lock : denote io_fs_handle → (exclusive : Bool := true) → LeanInitImpureExtern unit -- io_fs_handle.lock
  | lean_io_prim_handle_flush : denote io_fs_handle → LeanInitImpureExtern unit -- io_fs_handle.flush
  | lean_io_create_dir : denote system_filePath → LeanInitImpureExtern unit -- IO.FS.createDir
  | lean_io_timeit : (αt : MyTy) → String → denote (io αt) → LeanInitImpureExtern αt -- timeit
  | lean_runtime_forget : (αt : MyTy) → denote αt → LeanInitImpureExtern unit -- Runtime.forget
  | lean_io_prim_handle_put_str : denote io_fs_handle → String → LeanInitImpureExtern unit -- io_fs_handle.putStr
  | lean_io_app_path : LeanInitImpureExtern system_filePath -- IO.appPath
  | lean_io_mono_ms_now : LeanInitImpureExtern nat -- IO.monoMsNow
  | lean_io_realpath : denote system_filePath → LeanInitImpureExtern system_filePath -- IO.FS.realPath
  | lean_io_process_child_take_stdin : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitImpureExtern (prod (io_process_stdio_toHandleType cfg.stdin) (io_process_child {
    stdin := IO.Process.Stdio.null,
    stdout := cfg.stdout,
    stderr := cfg.stderr
  })) -- IO.Process.Child.takeStdin
  | lean_io_remove_dir : denote system_filePath → LeanInitImpureExtern unit -- IO.FS.removeDir
  | lean_io_prim_handle_truncate : denote io_fs_handle → LeanInitImpureExtern unit -- io_fs_handle.truncate
  | lean_io_as_task : (αt : MyTy) → denote (baseIO αt) → (prio : Task.Priority := Task.Priority.default) → LeanInitImpureExtern (task αt) -- BaseIO.asTask
  | lean_get_stdout : LeanInitImpureExtern io_fs_stream -- IO.getStdout
  | lean_io_metadata : denote system_filePath → LeanInitImpureExtern io_fs_metadata -- System.FilePath.metadata
  | lean_get_stdin : LeanInitImpureExtern io_fs_stream -- IO.getStdin
  | lean_io_hard_link : denote system_filePath → denote system_filePath → LeanInitImpureExtern unit -- IO.FS.hardLink
  | lean_io_process_spawn : (args : IO.Process.SpawnArgs) → LeanInitImpureExtern (io_process_child args.toStdioConfig) -- IO.Process.spawn
  | lean_io_prim_handle_get_line : denote io_fs_handle → LeanInitImpureExtern string -- io_fs_handle.getLine
  | lean_io_get_tid : LeanInitImpureExtern uint64 -- IO.getTID
  | lean_io_process_child_try_wait : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitImpureExtern (option uint32) -- IO.Process.Child.tryWait
  | lean_io_set_heartbeats : Nat → LeanInitImpureExtern unit -- IO.setNumHeartbeats
  | lean_runtime_hold : (αt : MyTy) → denote αt → LeanInitImpureExtern unit -- Runtime.hold
  | lean_io_prim_handle_write : denote io_fs_handle → denote byteArray → LeanInitImpureExtern unit -- io_fs_handle.write
  | lean_io_get_random_bytes : denote LeanPrimTy.usize → LeanInitImpureExtern byteArray -- IO.getRandomBytes
  | lean_io_bind_task : (αt : MyTy) → (βt : MyTy) → denote (task αt) → (denote αt → denote (baseIO (task βt))) → (prio : Task.Priority := Task.Priority.default) → (sync : Bool := false) → LeanInitImpureExtern (task βt) -- BaseIO.bindTask
  | lean_io_prim_handle_unlock : denote io_fs_handle → LeanInitImpureExtern unit -- io_fs_handle.unlock
  | lean_io_create_tempfile : LeanInitImpureExtern (prod io_fs_handle system_filePath) -- IO.FS.createTempFile
  | lean_io_check_canceled : LeanInitImpureExtern LeanPrimTy.bool -- IO.checkCanceled
  | lean_io_initializing : LeanInitImpureExtern LeanPrimTy.bool -- IO.initializing
  | lean_runtime_mark_multi_threaded : (αt : MyTy) → denote αt → LeanInitImpureExtern αt -- Runtime.markMultiThreaded
  | lean_io_create_tempdir : LeanInitImpureExtern system_filePath -- IO.FS.createTempDir
  | lean_io_get_task_state : (αt : MyTy) → denote (task αt) → LeanInitImpureExtern io_taskState -- IO.getTaskState
  | lean_runtime_mark_persistent : (αt : MyTy) → denote αt → LeanInitImpureExtern αt -- Runtime.markPersistent
  | lean_get_set_stdin : denote io_fs_stream → LeanInitImpureExtern io_fs_stream -- IO.setStdin
  | lean_io_process_get_pid : LeanInitImpureExtern uint32 -- IO.Process.getPID
  | lean_io_exit : (αt : MyTy) → UInt8 → LeanInitImpureExtern αt -- IO.Process.exit
  | lean_chmod : denote system_filePath → UInt32 → LeanInitImpureExtern unit -- IO.Prim.setAccessRights
  | lean_io_prim_handle_try_lock : denote io_fs_handle → (exclusive : Bool := true) → LeanInitImpureExtern LeanPrimTy.bool -- io_fs_handle.tryLock
  | lean_io_remove_file : denote system_filePath → LeanInitImpureExtern unit -- IO.FS.removeFile
  | lean_get_set_stdout : denote io_fs_stream → LeanInitImpureExtern io_fs_stream -- IO.setStdout
  | lean_io_symlink_metadata : denote system_filePath → LeanInitImpureExtern io_fs_metadata -- System.FilePath.symlinkMetadata
  | lean_get_stderr : LeanInitImpureExtern io_fs_stream -- IO.getStderr
  | lean_io_process_child_kill : {cfg : IO.Process.StdioConfig} → denote (io_process_child cfg) → LeanInitImpureExtern unit -- IO.Process.Child.kill
  | lean_io_process_get_current_dir : LeanInitImpureExtern system_filePath -- IO.Process.getCurrentDir
  | lean_io_current_dir : LeanInitImpureExtern system_filePath -- IO.currentDir
  | lean_io_wait : (αt : MyTy) → denote (task αt) → LeanInitImpureExtern αt -- IO.wait
  | lean_io_mono_nanos_now : LeanInitImpureExtern nat -- IO.monoNanosNow
  ---------------------------
  -- Init/System/Promise.lean
  ---------------------------
  | lean_io_promise_new : (αt : MyTy) → LeanInitImpureExtern (io_promise αt) -- IO.Promise.new
  | lean_io_promise_resolve : (αt : MyTy) → denote αt → denote (io_promise αt) → LeanInitImpureExtern unit -- IO.Promise.resolve

end LeanScript

end
