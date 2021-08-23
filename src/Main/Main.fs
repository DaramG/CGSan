open LLVM
open LLIR
open LLIR.Core
open Common
open System
open Analyzer

[<EntryPoint>]
let main argv =
  let m = Reader.readOne argv.[2]
  let prog = Lift.liftModule m
  let conf = Conf.ofEngine argv.[1]
  Logger.info "Start analysis"
  match argv.[0] with
  | "print" -> Pp.ppProg prog |> printfn "%s"
  | "test" -> Analyzer.test conf prog
  | _ -> Analyzer.analyze conf prog
  Logger.info "End analysis"
  0
