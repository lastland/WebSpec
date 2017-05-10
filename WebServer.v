Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.

Require Import Monad.
Require Import Buffer.
Require Import StringUtility.
Require Import FileSystem.
Require Import SimpleFileSystem.
Require Import Resource.
Require Import FSResource.
Require Import HttpdInterface.
Require Import SimpleHttpd.

Module fs := SimpleFS.
Module res := FSResource fs.
Module httpd := SimpleHttpd res.

Local Open Scope char_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.

Import ListNotations.

Definition get_method : string := "GET".
Definition head_method : string := "HEAD".

Definition http_not_found : nat := 404.
Definition http_ok : nat := 200.

Definition page : string := "<html><head><title>404 not found</title></head><body>404 not found</body></html>".
Definition page_len := length page.

Definition dir : string := "web/html/".

Definition file_reader (cls : res.class) (pos : nat) (max : nat) :
  string -> res.RS (nat * string) :=
  fun buf file_system =>
    match fs.fseek cls pos SeekSet file_system with
    | (_, file_system') =>
      match fs.fread cls 1 max file_system' with
      | ((b, r), file_system'') =>
        ((r, list_bits_to_string b), file_system'')
      end
    end.

Definition free_callback (cls: res.class) : res.RS unit :=
  fun file_system => match fs.fclose cls file_system with
                    (_, file_system') => (tt, file_system')
                  end.

(* Let's not consider ptr for now. *)
Definition open_file_and_get_stat (file_name : fs.path) :
  res.RS (option (fs.file * fs.file_stat)) :=
  file <- fs.fopen file_name rb;
  match file with
  | None => ret None
  | Some file => fd <- fs.fileno file;
                match fd with
                | None => fs.fclose file >> ret None
                | Some fd => file_system <- fs.get;
                            match fs.fstat fd file_system with
                            | None => fs.fclose file >> ret None
                            | Some stat => ret (Some (file, stat))
                            end
                end
  end.

Definition send_not_found (connection : httpd.connection): httpd.DM bool :=
  r <- httpd.create_response_from_buffer page_len Persistent page;
  match r with
  | (res, _) =>
    httpd.queue_response (Some connection) http_not_found res
  end.

Definition respond_file
           (cls : res.class) (connection : httpd.connection):
  httpd.DM (option bool) :=
  (* zero on the first argument is temporary. *)
  (* TODO: FIXME! *)
  r <- httpd.create_response_from_callback 0 (32 * 1024)
    file_reader cls free_callback;
  match r with
  | None => ret None
  | _ => b <- httpd.queue_response (Some connection) http_ok r;
               ret (Some b)
  end.

Definition ahc_echo (cls : res.class)
           (connection : httpd.connection)
           (url method version upload_data : string)
           (upload_data_size : nat) :
  httpd.daemon -> res.RS (bool * httpd.daemon) :=
  fun d =>
    if (strcmp method get_method && strcmp method head_method) then
      ret (false, d)
    else
      let file_name := dir ++ url in
      r <- open_file_and_get_stat file_name;
      match r with
      | None => ret (send_not_found connection d)
      | Some (file, stat) =>
        if fs.is_dir stat then
          fs.fclose file >> (
          r <- open_file_and_get_stat (file_name ++ "/index.html");
          match r with
          | None => ret (send_not_found connection d)
          | Some (file, stat) => 
            if fs.is_reg stat then
              match respond_file cls connection d with
              | (None, d') => fs.fclose file >> ret (false, d')
              | (Some b, d') => ret (b, d')
              end
            else
              fs.fclose file >> ret (send_not_found connection d)
          end)
        else if fs.is_reg stat then
               match respond_file cls connection d with
               | (None, d') => fs.fclose file >> ret (false, d')
               | (Some b, d') => ret (b, d')
               end
             else
               fs.fclose file >> ret (send_not_found connection d)
      end.
