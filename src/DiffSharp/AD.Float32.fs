//
// This file is part of
// DiffSharp: Differentiable Functional Programming
//
// Copyright (c) 2014--2016, National University of Ireland Maynooth (Atilim Gunes Baydin, Barak A. Pearlmutter)
// 
// Released under the LGPL license.
//
//   DiffSharp is free software: you can redistribute it and/or modify
//   it under the terms of the GNU Lesser General Public License as published by
//   the Free Software Foundation, either version 3 of the License, or
//   (at your option) any later version.
//
//   DiffSharp is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
//   GNU General Public License for more details.
//
//   You should have received a copy of the GNU Lesser General Public License
//   along with DiffSharp. If not, see <http://www.gnu.org/licenses/>.
//
// Written by:
//
//   Atilim Gunes Baydin
//   atilimgunes.baydin@nuim.ie
//
//   Barak A. Pearlmutter
//   barak@cs.nuim.ie
//
//   Brain and Computation Lab
//   Hamilton Institute & Department of Computer Science
//   National University of Ireland Maynooth
//   Maynooth, Co. Kildare
//   Ireland
//
//   www.bcl.hamilton.ie
//
/// Nested forward and reverse mode automatic differentiation module
module DiffSharp.AD.Float32

#nowarn "77"

open DiffSharp.Util
open DiffSharp.Config
open DiffSharp.Backend
open System.Threading.Tasks

let inline toNumber x = float32 x
let inline fail_with_invalid_type_message() = failwith "Unsupported type. Expecting D, float32, or int."

[<Literal>]
let internal numberMinus1 = -1.f

[<Literal>]
let internal number0_5 = 0.5f

[<Literal>]
let internal number0 = 0.f

[<Literal>]
let internal number1 = 1.f

[<Literal>]
let internal number2 = 2.f

type number = float32

type IDataBuffer = ISigmaDiffDataBuffer<number>

let inline Backend a : Backend<number> = global.DiffSharp.Config.GlobalConfig.BackendProvider.GetBackend(a).BackendHandle
let inline VisualizationContrast() = global.DiffSharp.Config.GlobalConfig.Float32VisualizationContrast
let inline FixedPointEpsilon() = global.DiffSharp.Config.GlobalConfig.Float32FixedPointEpsilon
let inline log10Val() = log10ValFloat32

// Scalar numeric type keeping dual numbers for forward mode and adjoints and tapes for reverse mode AD, with nesting capability, using tags to avoid perturbation confusion
[<CustomEquality; CustomComparison>]
type DNumber = 
    | D of number // Primal
    | DF of DNumber * DNumber * uint32 // Primal, tangent, tag
    | DR of DNumber * DNumber ref * TraceOp * uint32 ref * uint32 // Primal, adjoint, parent operation, fan-out counter, tag

    /// Primal value of this D
    member d.P = 
        match d with
        | D(_) -> d
        | DF(ap, _, _) -> ap
        | DR(ap, _, _, _, _) -> ap
    
    /// Deepest primal value of this D
    member d.PD = 
        let rec prec x = 
            match x with
            | D(_) -> x
            | DF(xp, _, _) -> prec xp
            | DR(xp, _, _, _, _) -> prec xp
        prec d
    
    /// Tangent value of this D
    member d.T = 
        match d with
        | D(_) -> D number0
        | DF(_, at, _) -> at
        | DR(_, _, _, _, _) -> failwith "Cannot get tangent value of DR."
    
    /// Adjoint value of this D
    member d.A 
        with get () = 
            match d with
            | D(_) -> D number0
            | DF(_, _, _) -> failwith "Cannot get adjoint value of DF."
            | DR(_, a, _, _, _) -> !a
        and set (v) = 
            match d with
            | D(_) -> ()
            | DF(_, _, _) -> failwith "Cannot set adjoint value of DF."
            | DR(_, a, _, _, _) -> a := v
    
    /// Fan-out counter of this D
    member d.F 
        with get () = 
            match d with
            | D(_) -> failwith "Cannot get fan-out value of D."
            | DF(_, _, _) -> failwith "Cannot get fan-out value of DF."
            | DR(_, _, _, f, _) -> !f
        and set (v) = 
            match d with
            | D(_) -> failwith "Cannot set fan-out value of D."
            | DF(_, _, _) -> failwith "Cannot set fan-out value of DF."
            | DR(_, _, _, f, _) -> f := v
    
    member d.Value
        with get() =
            let rec prec x = 
                match x with
                | D(p) -> p
                | DF(xp, _, _) -> prec xp
                | DR(xp, _, _, _, _) -> prec xp
            prec d

    member d.GetForward(t : DNumber, i : uint32) = DF(d, t, i)
    member d.GetReverse(i : uint32) = DR(d, ref (D number0), Noop, ref 0u, i)
    
    member d.Copy() = 
        match d with
        | D(ap) -> D(ap)
        | DF(ap, at, ai) -> DF(ap.Copy(), at.Copy(), ai)
        | DR(ap, aa, at, af, ai) -> DR(ap.Copy(), ref ((!aa).Copy()), at, ref (!af), ai)
    
    static member Zero = D number0
    static member One = D number1
    
    static member op_Explicit (d : DNumber) : number = 
        let rec prec x = 
            match x with
            | D(p) -> p
            | DF(xp, _, _) -> prec xp
            | DR(xp, _, _, _, _) -> prec xp
        prec d
    
    interface System.IComparable with
        member d.CompareTo(other) = 
            match other with
            | :? DNumber as d2 -> compare ((toNumber) d) ((toNumber) d2)
            | _ -> invalidArg "" "Cannot compare this D with another type."
    
    override d.Equals(other) = 
        match other with
        | :? DNumber as d2 -> compare ((toNumber) d) ((toNumber) d2) = 0
        | _ -> false
    
    override d.GetHashCode() = 
        match d with
        | D(ap) -> hash [| ap |]
        | DF(ap, at, ai) -> hash [| ap; at; ai |]
        | DR(ap, _, ao, _, ai) -> hash [| ap; ao; ai |]
    
    override d.ToString() = 
        let (d' : number) = DNumber.op_Explicit (d)
        match d with
        | D(_) -> sprintf "D % e" d'
        | DF(_) -> sprintf "DF % e" d'
        | DR(_) -> sprintf "DR % e" d'
    
    static member inline Op_D_D(a, ff, fd, df, r) = 
        match a with
        | D(ap) -> D(ff (ap))
        | DF(ap, at, ai) -> 
            let cp = fd (ap)
            DF(cp, df (cp, ap, at), ai)
        | DR(ap, _, _, _, ai) -> DR(fd (ap), ref (D number0), r (a), ref 0u, ai)
    
    static member inline Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | D(ap) -> 
            match b with
            | D(bp) -> D(ff (ap, bp))
            | DF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DF(cp, df_db (cp, bp, bt), bi)
            | DR(bp, _, _, _, bi) -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi)
        | DF(ap, at, ai) -> 
            match b with
            | D(_) -> 
                let cp = fd (ap, b)
                DF(cp, df_da (cp, ap, at), ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DR(ap, _, _, _, ai) -> 
            match b with
            | D(_) -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> DR(fd (ap, bp), ref (D number0), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member (+) (a : DNumber, b : DNumber) = 
        let inline ff (a, b) = a + b
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = bt
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_D_D(a, b)
        let inline r_d_c (a, b) = Add_D_DCons(a)
        let inline r_c_d (a, b) = Add_D_DCons(b)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (-) (a : DNumber, b : DNumber) = 
        let inline ff (a, b) = a - b
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = -bt
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_D_D(a, b)
        let inline r_d_c (a, b) = Sub_D_DCons(a)
        let inline r_c_d (a, b) = Sub_DCons_D(b)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (*) (a : DNumber, b : DNumber) = 
        let inline ff (a, b) = a * b
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = at * bp + ap * bt
        let inline r_d_d (a, b) = Mul_D_D(a, b)
        let inline r_d_c (a, b) = Mul_D_DCons(a, b)
        let inline r_c_d (a, b) = Mul_D_DCons(b, a)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (/) (a : DNumber, b : DNumber) = 
        let inline ff (a, b) = a / b
        let inline fd (a, b) = a / b
        let inline df_da (cp, ap, at) = at / b
        let inline df_db (cp, bp, bt) = -bt * cp / bp // cp = a / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt * cp) / bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_D_D(a, b)
        let inline r_d_c (a, b) = Div_D_DCons(a, b)
        let inline r_c_d (a, b) = Div_DCons_D(a, b)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Pow(a : DNumber, b : DNumber) = 
        let inline ff (a, b) = a ** b
        let inline fd (a, b) = a ** b
        let inline df_da (cp, ap, at) = at * (ap ** (b - D number1)) * b
        let inline df_db (cp, bp, bt) = bt * cp * log a // cp = a ** bp
        let inline df_dab (cp, ap, at, bp, bt) = (ap ** (bp - D number1)) * (at * bp + ap * bt * log ap)
        let inline r_d_d (a, b) = Pow_D_D(a, b)
        let inline r_d_c (a, b) = Pow_D_DCons(a, b)
        let inline r_c_d (a, b) = Pow_DCons_D(a, b)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Atan2(a : DNumber, b : DNumber) = 
        let inline ff (a, b) = atan2 a b
        let inline fd (a, b) = atan2 a b
        let inline df_da (cp, ap, at) = at * b / (ap * ap + b * b)
        let inline df_db (cp, bp, bt) = -bt * a / (a * a + bp * bp)
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp - bt * ap) / (ap * ap + bp * bp)
        let inline r_d_d (a, b) = Atan2_D_D(a, b)
        let inline r_d_c (a, b) = Atan2_D_DCons(a, b)
        let inline r_c_d (a, b) = Atan2_DCons_D(a, b)
        DNumber.Op_D_D_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    // D - number binary operations
    static member (+) (a : DNumber, b : number) = a + (D b)
    static member (-) (a : DNumber, b : number) = a - (D b)
    static member (*) (a : DNumber, b : number) = a * (D b)
    static member (/) (a : DNumber, b : number) = a / (D b)
    static member Pow(a : DNumber, b : number) = a ** (D b)
    static member Atan2(a : DNumber, b : number) = atan2 a (D b)
    // number - D binary operations
    static member (+) (a : number, b : DNumber) = (D a) + b
    static member (-) (a : number, b : DNumber) = (D a) - b
    static member (*) (a : number, b : DNumber) = (D a) * b
    static member (/) (a : number, b : DNumber) = (D a) / b
    static member Pow(a : number, b : DNumber) = (D a) ** b
    static member Atan2(a : number, b : DNumber) = atan2 (D a) b
    // D - int binary operations
    static member (+) (a : DNumber, b : int) = a + (D(toNumber b))
    static member (-) (a : DNumber, b : int) = a - (D(toNumber b))
    static member (*) (a : DNumber, b : int) = a * (D(toNumber b))
    static member (/) (a : DNumber, b : int) = a / (D(toNumber b))
    static member Pow(a : DNumber, b : int) = a ** (D(toNumber b))
    static member Atan2(a : DNumber, b : int) = atan2 a (D(toNumber b))
    // int - D binary operations
    static member (+) (a : int, b : DNumber) = (D(toNumber a)) + b
    static member (-) (a : int, b : DNumber) = (D(toNumber a)) - b
    static member (*) (a : int, b : DNumber) = (D(toNumber a)) * b
    static member (/) (a : int, b : DNumber) = (D(toNumber a)) / b
    static member Pow(a : int, b : DNumber) = (D(toNumber a)) ** b
    static member Atan2(a : int, b : DNumber) = atan2 (D(toNumber a)) b
    
    static member Log(a : DNumber) = 
        let inline ff (a) = log a
        let inline fd (a) = log a
        let inline df (cp, ap, at) = at / ap
        let inline r (a) = Log_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Log10(a : DNumber) = 
        let inline ff (a) = log10 a
        let inline fd (a) = log10 a
        let inline df (cp, ap : DNumber, at) = at / (ap * log10Val())
        let inline r (a) = Log10_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Exp(a : DNumber) = 
        let inline ff (a) = exp a
        let inline fd (a) = exp a
        let inline df (cp, ap, at) = at * cp // cp = exp ap
        let inline r (a) = Exp_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Sin(a : DNumber) = 
        let inline ff (a) = sin a
        let inline fd (a) = sin a
        let inline df (cp, ap, at) = at * cos ap
        let inline r (a) = Sin_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Cos(a : DNumber) = 
        let inline ff (a) = cos a
        let inline fd (a) = cos a
        let inline df (cp, ap, at) = -at * sin ap
        let inline r (a) = Cos_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Tan(a : DNumber) = 
        let inline ff (a) = tan a
        let inline fd (a) = tan a
        
        let inline df (cp, ap, at) = 
            let cosa = cos ap
            at / (cosa * cosa)
        
        let inline r (a) = Tan_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member (~-) (a : DNumber) = 
        let inline ff (a) = -a
        let inline fd (a) = -a
        let inline df (cp, ap, at) = -at
        let inline r (a) = Neg_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Sqrt(a : DNumber) = 
        let inline ff (a) = sqrt a
        let inline fd (a) = sqrt a
        let inline df (cp, ap, at) = at / ((D number2) * cp) // cp = sqrt ap
        let inline r (a) = Sqrt_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Sinh(a : DNumber) = 
        let inline ff (a) = sinh a
        let inline fd (a) = sinh a
        let inline df (cp, ap, at) = at * cosh ap
        let inline r (a) = Sinh_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Cosh(a : DNumber) = 
        let inline ff (a) = cosh a
        let inline fd (a) = cosh a
        let inline df (cp, ap, at) = at * sinh ap
        let inline r (a) = Cosh_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Tanh(a : DNumber) = 
        let inline ff (a) = tanh a
        let inline fd (a) = tanh a
        
        let inline df (cp, ap, at) = 
            let cosha = cosh ap
            at / (cosha * cosha)
        
        let inline r (a) = Tanh_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Asin(a : DNumber) = 
        let inline ff (a) = asin a
        let inline fd (a) = asin a
        let inline df (cp, ap, at) = at / sqrt (D number1 - ap * ap)
        let inline r (a) = Asin_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Acos(a : DNumber) = 
        let inline ff (a) = acos a
        let inline fd (a) = acos a
        let inline df (cp, ap, at) = -at / sqrt (D number1 - ap * ap)
        let inline r (a) = Acos_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Atan(a : DNumber) = 
        let inline ff (a) = atan a
        let inline fd (a) = atan a
        let inline df (cp, ap, at) = at / (D number1 + ap * ap)
        let inline r (a) = Atan_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Abs(a : DNumber) = 
        let inline ff (a) = abs a
        let inline fd (a) = abs a
        let inline df (cp, ap, at) = at * DNumber.Sign(ap)
        let inline r (a) = Abs_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Sign(a : DNumber) = 
        let inline ff (a) = signummod a
        let inline fd (a) = DNumber.Sign(a)
        let inline df (cp, ap, at) = D number0
        let inline r (a) = Sign_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Floor(a : DNumber) = 
        let inline ff (a) = floor a
        let inline fd (a) = floor a
        let inline df (cp, ap, at) = D number0
        let inline r (a) = Floor_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Ceiling(a : DNumber) = 
        let inline ff (a) = ceil a
        let inline fd (a) = ceil a
        let inline df (cp, ap, at) = D number0
        let inline r (a) = Ceil_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Round(a : DNumber) = 
        let inline ff (a) = round a
        let inline fd (a) = round a
        let inline df (cp, ap, at) = D number0
        let inline r (a) = Round_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member ReLU(a : DNumber) = 
        let inline ff (a) = max number0 a
        let inline fd (a) = DNumber.ReLU(a)
        let inline df (cp, ap, at : DNumber) = at * (number1 + DNumber.Sign(ap)) / number2
        let inline r (a) = ReLU_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member Sigmoid(a : DNumber) = 
        let inline ff (a) = number1 / (number1 + exp -a)
        let inline fd (a) = DNumber.Sigmoid(a)
        let inline df (cp : DNumber, ap, at) = at * cp * (number1 - cp)
        let inline r (a) = Sigmoid_D(a)
        DNumber.Op_D_D(a, ff, fd, df, r)
    
    static member SoftPlus(a : DNumber) = log (number1 + exp a)
    static member SoftSign(a : DNumber) = a / (number1 + abs a)
    static member LogSumExp(a : DNumber) = a
    static member Max(a : DNumber, b : DNumber) = ((a + b) + abs (b - a)) / number2
    static member Min(a : DNumber, b : DNumber) = ((a + b) - abs (a - b)) / number2
    static member FixedPoint (g : DNumber -> DNumber -> DNumber) (a0 : DNumber) (b : DNumber) = 
        let imax = DiffSharp.Config.GlobalConfig.FixedPointMaxIterations
        let eps = D(FixedPointEpsilon())
        let mutable a = a0
        let mutable i = 0
        match b with
        | D(bp) -> 
            while i < imax do
                i <- i + 1
                if i >= imax then 
                    //printfn "Fixed point iteration timeout, i = %i" i
                    ignore()
                else 
                    let aa = g a b
                    if abs (aa - a) <= eps then 
                        //printfn "Fixed point iteration converged, i = %i" i
                        i <- imax
                    a <- aa
            D(toNumber a)
        | DF(bp, bt, bi) -> 
            while i < imax do
                i <- i + 1
                if i >= imax then 
                    //printfn "Fixed point iteration timeout, i = %i" i
                    ignore()
                else 
                    let aa = g a b
                    if (abs (aa.P - a.P) <= eps) && (abs (aa.T - a.T) <= eps) then 
                        //printfn "Fixed point iteration converged, i = %i" i
                        i <- imax
                    a <- aa
            DF(a.P, a.T, bi)
        | DR(bp, _, _, _, bi) -> 
            let bfirst = DR(bp, ref (D number0), Noop, ref 0u, bi) // Cut the connection between b and bfirst ("switch of graph construction" involving b beyond this point)
            while i < imax do
                i <- i + 1
                if i >= imax then 
                    //printfn "Fixed point iteration timeout, i = %i" i
                    ignore()
                else 
                    let aa = g a bfirst
                    if abs (aa - a) <= eps then 
                        //printfn "Fixed point iteration converged, i = %i" i
                        i <- imax
                    a <- aa
            let aprev = DR(a.P, ref (D number0), Noop, ref 0u, bi)
            let alast = g aprev bfirst
            DR(a.P, ref (D number0), FixedPoint_D(b, bfirst, aprev, alast), ref 0u, bi)

/// Vector numeric type keeping dual numbers for forward mode and adjoints and tapes for reverse mode AD, with nesting capability, using tags to avoid perturbation confusion
and DVector = 
    | DV of IDataBuffer // Primal
    | DVF of DVector * DVector * uint32 // Primal, tangent, tag
    | DVR of DVector * DVector ref * TraceOp * uint32 ref * uint32 // Primal, adjoint, parent operation, fan-out counter, tag
    
    /// Primal value of this DV
    member d.P = 
        match d with
        | DV(_) -> d
        | DVF(ap, _, _) -> ap
        | DVR(ap, _, _, _, _) -> ap
    
    /// Deepest primal value of this DV
    member d.PD = 
        let rec prec x = 
            match x with
            | DV(_) -> x
            | DVF(xp, _, _) -> prec xp
            | DVR(xp, _, _, _, _) -> prec xp
        prec d
    
    /// Tangent value of this DV
    member d.T = 
        match d with
        | DV(_) -> DVector.ZeroN d.Length
        | DVF(_, at, _) -> at
        | DVR(_, _, _, _, _) -> failwith "Cannot get tangent value of DVR."
    
    /// Adjoint value of this DV
    member d.A 
        with get () = 
            match d with
            | DV(_) -> DVector.ZeroN d.Length
            | DVF(_, _, _) -> failwith "Cannot get adjoint value of DVF."
            | DVR(_, a, _, _, _) -> !a
        and set (v) = 
            match d with
            | DV(_) -> ()
            | DVF(_, _, _) -> failwith "Cannot set adjoint value of DVF."
            | DVR(_, a, _, _, _) -> a := v
    
    /// Fan-out counter of this DV
    member d.F 
        with get () = 
            match d with
            | DV(_) -> failwith "Cannot get fan-out value of DV."
            | DVF(_, _, _) -> failwith "Cannot get fan-out value of DVF."
            | DVR(_, _, _, f, _) -> !f
        and set (v) = 
            match d with
            | DV(_) -> failwith "Cannot set fan-out value of DV."
            | DVF(_, _, _) -> failwith "Cannot set fan-out value of DVF."
            | DVR(_, _, _, f, _) -> f := v
    
    member d.Buffer = 
        let rec prec x = 
            match x with
            | DV(p) -> p
            | DVF(xp, _, _) -> prec xp
            | DVR(xp, _, _, _, _) -> prec xp
        
        let data = (prec d)
        data
    
    member d.GetForward(t : DVector, i : uint32) = DVF(d, t, i)
    member d.GetReverse(i : uint32) = DVR(d, ref (DVector.ZeroN d.Length), Noop, ref 0u, i)
    
    member d.ShallowCopy() = 
        match d with
        | DV(ap) -> DV(ap.ShallowCopy())
        | DVF(ap, at, ai) -> DVF(ap.ShallowCopy(), at.ShallowCopy(), ai)
        | DVR(ap, aa, at, af, ai) -> DVR(ap.ShallowCopy(), ref ((!aa).ShallowCopy()), at, ref (!af), ai)
    
    member d.DeepCopy() = 
        match d with
        | DV(ap) -> DV(ap.DeepCopy())
        | DVF(ap, at, ai) -> DVF(ap.DeepCopy(), at.DeepCopy(), ai)
        | DVR(ap, aa, at, af, ai) -> DVR(ap.DeepCopy(), ref ((!aa).DeepCopy()), at, ref (!af), ai)
    
    member d.Length = 
        match d with
        | DV(ap) -> ap.Length
        | DVF(ap, _, _) -> ap.Length
        | DVR(ap, _, _, _, _) -> ap.Length
    
    member d.Item 
        with get i = 
            match d with
            | DV(ap) -> D(ap.SubData.[i])
            | DVF(ap, at, ai) -> DF(ap.[i], at.[i], ai)
            | DVR(ap, _, _, _, ai) -> DR(ap.[i], ref (D number0), Item_DV(d, i), ref 0u, ai)
    
    member d.ToRowDM(backend : Backend<number>) = 
        match d with
        | DV(ap) -> 
            DNDArray.OfNumberArray(1, 
                                   seq [ ap.SubData ]
                                   |> Seq.concat
                                   |> Seq.toArray,
                                   backend)
        | DVF(ap, at, ai) -> DMF(ap.ToRowDM(backend), at.ToRowDM(backend), ai)
        | DVR(ap, _, _, _, ai) -> 
            let cp = ap.ToRowDM(backend)
            DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), RowMatrix_DV(d), ref 0u, ai)
    
    member d.ToColDM(backend : Backend<number>) = DNDArray.Transpose(d.ToRowDM(backend))
    
    member d.GetSlice(lower, upper) = 
        let l = defaultArg lower 0
        let u = defaultArg upper (d.Length - 1)
        match d with
        | DV(ap) -> DV(ap.GetValues l (u - l + 1))
        | DVF(ap, at, ai) -> DVF(ap.[l..u], at.[l..u], ai)
        | DVR(ap, _, _, _, ai) -> 
            let cp = ap.[l..u]
            DVR(cp, ref (DVector.ZeroN cp.Length), Slice_DV(d, l), ref 0u, ai)
    
    member d.ToArray() = 
        match d with
        | DV(ap) -> ap.SubData |> Array.map D
        | DVF(ap, at, ai) -> Array.init ap.Length (fun i -> DF(ap.[i], at.[i], ai))
        | DVR(ap, _, _, _, ai) -> Array.init ap.Length (fun i -> DR(ap.[i], ref (D number0), Item_DV(d, i), ref 0u, ai))
    
    override d.ToString() = 
        let (d' : number []) = DVector.op_Explicit (d)
        let sb = System.Text.StringBuilder()
        match d with
        | DV(_) -> sb.AppendLine(sprintf "DV : %i" d.Length) |> ignore
        | DVF(_) -> sb.AppendLine(sprintf "DVF: %i" d.Length) |> ignore
        | DVR(_) -> sb.AppendLine(sprintf "DVR: %i" d.Length) |> ignore
        for i = 0 to d.Length - 1 do
            sb.Append(sprintf "% 9.3g " d'.[i]) |> ignore
        sb.ToString()
    
    member d.ToMathematicaString() = 
        let (d' : number []) = DVector.op_Explicit (d)
        let sb = System.Text.StringBuilder()
        sb.Append("{") |> ignore
        for i = 0 to d.Length - 1 do
            sb.Append(sprintf "%.2f" d'.[i]) |> ignore
            if i < d.Length - 1 then sb.Append(", ") |> ignore
        sb.Append("}") |> ignore
        sb.ToString()
    
    member d.ToMatlabString() = 
        let (d' : number []) = DVector.op_Explicit (d)
        let sb = System.Text.StringBuilder()
        sb.Append("[") |> ignore
        for i = 0 to d.Length - 1 do
            sb.Append(sprintf "%.2f" d'.[i]) |> ignore
            if i < d.Length - 1 then sb.Append(" ") |> ignore
        sb.Append("]") |> ignore
        sb.ToString()
    
    static member Zero = DV(new NativeDataBuffer<number>(Array.empty))
    static member ZeroN n = DV(new NativeDataBuffer<number>((Array.zeroCreate n)))
    
    static member op_Explicit (d : DVector) : number [] = 
        let rec prec x = 
            match x with
            | DV(p) -> p
            | DVF(xp, _, _) -> prec xp
            | DVR(xp, _, _, _, _) -> prec xp
        
        let data = (prec d)
        data.SubData
    
    static member op_Explicit (d) = DV(d)
    
    static member OfArray(a : DNumber []) = 
        // TODO: check to ensure that all elements in the array are of the same type (D, DF, or DR) and have the same nesting tag
        match a.[0] with
        | D(_) -> DV(Backend(a.[0]).CreateDataBuffer(a |> Array.map toNumber))
        | DF(_, _, ai) -> 
            let ap = a |> Array.map (fun x -> x.P)
            let at = a |> Array.map (fun x -> x.T)
            DVF(DVector.OfArray(ap), DVector.OfArray(at), ai)
        | DR(_, _, _, _, ai) -> 
            let ap = a |> Array.map (fun x -> x.P)
            let cp = DVector.OfArray(ap)
            DVR(cp, ref (DVector.ZeroN cp.Length), Make_DV_ofDs(a), ref 0u, ai)
    
    static member Split(d : DVector, n : seq<int>) = 
        match d with
        | DV(ap) -> 
            seq { 
                let i = ref 0
                for j in n do
                    yield DV(Backend(d).CreateDataBuffer(Array.sub ap.SubData !i j))
                    i := !i + j
            }
        | DVF(ap, at, ai) -> 
            let aps = DVector.Split(ap, n)
            let ats = DVector.Split(at, n)
            Seq.map2 (fun p t -> DVF(p, t, ai)) aps ats
        | DVR(ap, _, _, _, ai) -> 
            let aps = DVector.Split(ap, n)
            
            let ii = 
                n
                |> Seq.mapFold (fun s i -> s, s + i) 0
                |> fst
                |> Array.ofSeq
            Seq.mapi (fun i p -> DVR(p, ref (DVector.ZeroN p.Length), Split_DV(d, ii.[i]), ref 0u, ai)) aps
    
    static member inline Op_DV_DV(a, ff, fd, df, r) = 
        match a with
        | DV(ap) -> DV(ff (ap))
        | DVF(ap, at, ai) -> 
            let cp = fd (ap)
            DVF(cp, df (cp, ap, at), ai)
        | DVR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DVR(cp, ref (DVector.ZeroN cp.Length), r (a), ref 0u, ai)
    
    static member inline Op_DV_DM(a, ff, fd, df, r) = 
        match a with
        | DV(ap) -> DM(ff (ap))
        | DVF(ap, at, ai) -> 
            let cp = fd (ap)
            DMF(cp, df (cp, ap, at), ai)
        | DVR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r (a), ref 0u, ai)
    
    static member inline Op_DV_D(a, ff, fd, df, r) = 
        match a with
        | DV(ap) -> D(ff (ap))
        | DVF(ap, at, ai) -> 
            let cp = fd (ap)
            DF(cp, df (cp, ap, at), ai)
        | DVR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DR(cp, ref (D number0), r (a), ref 0u, ai)
    
    static member inline Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | DV(bp) -> DV(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DVF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DV_DV_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | DV(bp) -> DM(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DV_DV_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | DV(bp) -> D(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> DR(fd (ap, bp), ref (D number0), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> DR(fd (a, bp), ref (D number0), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> DR(fd (ap, b), ref (D number0), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | D(bp) -> DV(ff (ap, bp))
            | DF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DVF(cp, df_db (cp, bp, bt), bi)
            | DR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | D(_) -> 
                let cp = fd (ap, b)
                DVF(cp, df_da (cp, ap, at), ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | D(_) -> 
                let cp = fd (ap, b)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | D(ap) -> 
            match b with
            | DV(bp) -> DV(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DVF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi)
        | DF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    /// Element-wise addition of `a` and `b`
    static member (+) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Add_V_V(a, b)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = bt
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DV_DV(a, b)
        let inline r_d_c (a, b) = Add_DV_DVCons(a)
        let inline r_c_d (a, b) = Add_DV_DVCons(b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise subtraction of `a` and `b`
    static member (-) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Sub_V_V(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = -bt
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_DV_DV(a, b)
        let inline r_d_c (a, b) = Sub_DV_DVCons(a)
        let inline r_c_d (a, b) = Sub_DVCons_DV(b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Inner (dot, scalar) product of `a` and `b`
    static member (*) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Mul_Dot_V_V(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_Dot_DV_DV(a, b)
        let inline r_d_c (a, b) = Mul_Dot_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Mul_Dot_DV_DVCons(b, a)
        DVector.Op_DV_DV_D(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise (Hadamard, Schur) product of `a` and `b`
    static member (.*) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map2_F_V_V((*), a, b)
        let inline fd (a, b) = a .* b
        let inline df_da (cp, ap, at) = at .* b
        let inline df_db (cp, bp, bt) = a .* bt
        let inline df_dab (cp, ap, at, bp, bt) = (at .* bp) + (ap .* bt)
        let inline r_d_d (a, b) = Mul_Had_DV_DV(a, b)
        let inline r_d_c (a, b) = Mul_Had_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Mul_Had_DV_DVCons(b, a)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Outer (dyadic, tensor) product of `a` and `b`
    static member (&*) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Mul_Out_V_V(a, b)
        let inline fd (a, b) = a &* b
        let inline df_da (cp, ap, at) = at &* b
        let inline df_db (cp, bp, bt) = a &* bt
        let inline df_dab (cp, ap, at, bp, bt) = (at &* bp) + (ap &* bt)
        let inline r_d_d (a, b) = Mul_Out_DV_DV(a, b)
        let inline r_d_c (a, b) = Mul_Out_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Mul_Out_DVCons_DV(a, b)
        DVector.Op_DV_DV_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise (Hadamard, Schur) division of `a` and `b`
    static member (./) (a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map2_F_V_V((/), a, b)
        let inline fd (a, b) = a ./ b
        let inline df_da (cp, ap, at) = at ./ b
        let inline df_db (cp, bp, bt) = -bt .* cp ./ bp // cp = ap / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt .* cp) ./ bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_Had_DV_DV(a, b)
        let inline r_d_c (a, b) = Div_Had_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Div_Had_DVCons_DV(a, b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise power of `a` and `b`
    static member Pow(a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map2_F_V_V((fun x y -> x ** y), a, b)
        let inline fd (a, b) = a ** b
        let inline df_da (cp, ap, at) = at .* (ap ** (b - D number1)) .* b
        let inline df_db (cp, bp, bt) = bt .* cp .* log a // cp = a ** bp
        let inline df_dab (cp, ap, at, bp, bt) = (ap ** (bp - D number1)) .* ((at .* bp) + (ap .* bt .* log ap))
        let inline r_d_d (a, b) = Pow_DV_DV(a, b)
        let inline r_d_c (a, b) = Pow_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Pow_DVCons_DV(a, b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise atan2 of `a` and `b`
    static member Atan2(a : DVector, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map2_F_V_V(atan2, a, b)
        let inline fd (a, b) = atan2 a b
        let inline df_da (cp, ap, at) = (at .* b) ./ ((ap .* ap) + (b .* b))
        let inline df_db (cp, bp, bt) = (-bt .* a) ./ ((a .* a) + (bp .* bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at .* bp) - (bt .* ap)) ./ ((ap .* ap) + (bp .* bp))
        let inline r_d_d (a, b) = Atan2_DV_DV(a, b)
        let inline r_d_c (a, b) = Atan2_DV_DVCons(a, b)
        let inline r_c_d (a, b) = Atan2_DVCons_DV(a, b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Multiply vector `a` by scalar `b`
    static member (*) (a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Mul_S_V(b, a)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DV_D(a, b)
        let inline r_d_c (a, b) = Mul_DV_DCons(a, b)
        let inline r_c_d (a, b) = Mul_DVCons_D(a, b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Multiply vector `b` by scalar `a`
    static member (*) (a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Mul_S_V(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DV_D(b, a)
        let inline r_d_c (a, b) = Mul_DVCons_D(b, a)
        let inline r_c_d (a, b) = Mul_DV_DCons(b, a)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Divide vector `a` by scalar `b`
    static member (/) (a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Mul_S_V(number1 / b, a)
        let inline fd (a, b) = a / b
        let inline df_da (cp, ap, at) = at / b
        let inline df_db (cp, bp, bt) = -bt * cp / bp // cp = a / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt * cp) / bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_DV_D(a, b)
        let inline r_d_c (a, b) = Div_DV_DCons(a, b)
        let inline r_c_d (a, b) = Div_DVCons_D(a, b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where each element is scalar `a` divided by the corresponding element of vector `b`
    static member (/) (a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map_F_V((fun v -> a / v), b)
        let inline fd (a, b) = a / b
        let inline df_da (cp, ap, at) = at / b
        let inline df_db (cp, bp, bt) = -bt .* (cp ./ bp) // cp = a / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt * cp) / bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_D_DV(a, b)
        let inline r_d_c (a, b) = Div_D_DVCons(a, b)
        let inline r_c_d (a, b) = Div_DCons_DV(a, b)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add scalar `b` to vector `a`
    static member (+) (a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Add_S_V(b, a)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DVector.OfArray(Array.create a.Length bt)
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DV_D(a, b)
        let inline r_d_c (a, b) = Add_DV_DCons(a)
        let inline r_c_d (a, b) = Add_DVCons_D(b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add scalar `a` to vector `b`
    static member (+) (a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Add_S_V(a, b)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = DVector.OfArray(Array.create b.Length at)
        let inline df_db (cp, bp, bt) = bt
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DV_D(b, a)
        let inline r_d_c (a, b) = Add_DVCons_D(a)
        let inline r_c_d (a, b) = Add_DV_DCons(b)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Subtract scalar `b` from vector `a`
    static member (-) (a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Sub_V_S(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DVector.OfArray(Array.create a.Length -bt)
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_DV_D(a, b)
        let inline r_d_c (a, b) = Sub_DV_DCons(a)
        let inline r_c_d (a, b) = Sub_DVCons_D(b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where each element is the corresponding element of vector `b` subtracted from scalar `a`
    static member (-) (a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Sub_S_V(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = DVector.OfArray(Array.create b.Length at)
        let inline df_db (cp, bp, bt) = -bt
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_D_DV(a, b)
        let inline r_d_c (a, b) = Sub_D_DVCons(a)
        let inline r_c_d (a, b) = Sub_DCons_DV(b)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where each corresponding element of vector `a` is raised to the power of scalar `b`
    static member Pow(a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Map_F_V((fun v -> v ** b), a)
        let inline fd (a, b) = a ** b
        let inline df_da (cp, ap : DVector, at : DVector) = at .* (ap ** (b - D number1)) * b
        let inline df_db (cp, bp, bt) = bt * cp .* log a // cp = a ** bp
        let inline df_dab (cp, ap : DVector, at : DVector, bp : DNumber, bt : DNumber) = 
            (ap ** (bp - D number1)) .* ((at * bp) + (ap * bt .* log ap))
        let inline r_d_d (a, b) = Pow_DV_D(a, b)
        let inline r_d_c (a, b) = Pow_DV_DCons(a, b)
        let inline r_c_d (a, b) = Pow_DVCons_D(a, b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where scalar `a` is raised to the power of each corresponding element of vector `b`
    static member Pow(a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map_F_V((fun v -> a ** v), b)
        let inline fd (a : DNumber, b : DVector) = DVector.Pow(a, b)
        let inline df_da (cp, ap : DNumber, at : DNumber) = (at * (DVector.Pow(ap, b - D number1))) .* b
        let inline df_db (cp, bp, bt) = bt .* cp * log a // cp = a ** bp
        let inline df_dab (cp, ap : DNumber, at : DNumber, bp : DVector, bt : DVector) = 
            (DVector.Pow(ap, bp - D number1)) .* ((at * bp) + (ap * bt * log ap))
        let inline r_d_d (a, b) = Pow_D_DV(a, b)
        let inline r_d_c (a, b) = Pow_D_DVCons(a, b)
        let inline r_c_d (a, b) = Pow_DCons_DV(a, b)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where each corresponding element of vector `a` is raised to the power of scalar `b`
    static member Atan2(a : DVector, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Map_F_V((fun v -> atan2 v b), a)
        let inline fd (a : DVector, b : DNumber) = DVector.Atan2(a, b)
        let inline df_da (cp, ap, at) = (at * b) ./ ((ap .* ap) + (b * b))
        let inline df_db (cp, bp, bt) = (-bt * a) ./ ((a .* a) + (bp * bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at * bp) - (bt * ap)) ./ ((ap .* ap) + (bp * bp))
        let inline r_d_d (a, b) = Atan2_DV_D(a, b)
        let inline r_d_c (a, b) = Atan2_DV_DCons(a, b)
        let inline r_c_d (a, b) = Atan2_DVCons_D(a, b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Generate a vector where scalar `a` is raised to the power of each corresponding element of vector `b`
    static member Atan2(a : DNumber, b : DVector) = 
        let inline ff (a, b) = Backend(a).Map_F_V((fun v -> atan2 a v), b)
        let inline fd (a : DNumber, b : DVector) = DVector.Atan2(a, b)
        let inline df_da (cp, ap, at) = (at * b) ./ ((ap * ap) + (b .* b))
        let inline df_db (cp, bp, bt) = (-bt * a) ./ ((a * a) + (bp .* bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at * bp) - (bt * ap)) ./ ((ap * ap) + (bp .* bp))
        let inline r_d_d (a, b) = Atan2_D_DV(a, b)
        let inline r_d_c (a, b) = Atan2_D_DVCons(a, b)
        let inline r_c_d (a, b) = Atan2_DCons_DV(a, b)
        DVector.Op_D_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add scalar `b` to vector `a` at index `i`
    static member AddItem(a : DVector, i : int, b : DNumber) = 
        let inline ff (a : IDataBuffer, b) = 
            let aa = a.DeepCopy()
            aa.SubData.[i] <- aa.SubData.[i] + b
            aa
        
        let inline fd (a, b) = DVector.AddItem(a, i, b)
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DVector.AddItem(DVector.ZeroN a.Length, i, bt)
        let inline df_dab (cp, ap, at, bp, bt) = DVector.AddItem(at, i, bt)
        let inline r_d_d (a, b) = AddItem_DV_D(a, i, b)
        let inline r_d_c (a, b) = AddItem_DV_DCons(a)
        let inline r_c_d (a, b) = AddItem_DVCons_D(i, b)
        DVector.Op_DV_D_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add subvector `b` to vector `a`, starting from index `i`
    static member AddSubVector(a : DVector, i : int, b : DVector) = 
        let inline ff (a : IDataBuffer, b : IDataBuffer) = 
            let aa = a.DeepCopy()
            for j = 0 to b.Length - 1 do
                aa.SubData.[i + j] <- aa.SubData.[i + j] + b.SubData.[j]
            aa
        
        let inline fd (a, b) = DVector.AddSubVector(a, i, b)
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DVector.AddSubVector(DVector.ZeroN a.Length, i, bt)
        let inline df_dab (cp, ap, at, bp, bt) = DVector.AddSubVector(at, i, bt)
        let inline r_d_d (a, b) = AddSubVector_DV_DV(a, i, b)
        let inline r_d_c (a, b) = AddSubVector_DV_DVCons(a)
        let inline r_c_d (a, b) = AddSubVector_DVCons_DV(i, b)
        DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    // DV - number binary operations
    static member (+) (a : DVector, b : number) = a + D b
    static member (-) (a : DVector, b : number) = a - D b
    static member (*) (a : DVector, b : number) = a * D b
    static member (/) (a : DVector, b : number) = a / D b
    static member Pow(a : DVector, b : number) = a ** D b
    static member Atan2(a : DVector, b : number) = DVector.Atan2(a, D b)
    // number - DV binary operations
    static member (+) (a : number, b : DVector) = (D a) + b
    static member (-) (a : number, b : DVector) = (D a) - b
    static member (*) (a : number, b : DVector) = (D a) * b
    static member (/) (a : number, b : DVector) = (D a) / b
    static member Pow(a : number, b : DVector) = DVector.Pow(D a, b)
    static member Atan2(a : number, b : DVector) = DVector.Atan2(D a, b)
    // DV - int binary operations
    static member (+) (a : DVector, b : int) = a + D(toNumber b)
    static member (-) (a : DVector, b : int) = a - D(toNumber b)
    static member (*) (a : DVector, b : int) = a * D(toNumber b)
    static member (/) (a : DVector, b : int) = a / D(toNumber b)
    static member Pow(a : DVector, b : int) = a ** D(toNumber b)
    static member Atan2(a : DVector, b : int) = DVector.Atan2(a, D(toNumber b))
    // int - DV binary operations
    static member (+) (a : int, b : DVector) = (D(toNumber a)) + b
    static member (-) (a : int, b : DVector) = (D(toNumber a)) - b
    static member (*) (a : int, b : DVector) = (D(toNumber a)) * b
    static member (/) (a : int, b : DVector) = (D(toNumber a)) / b
    static member Pow(a : int, b : DVector) = DVector.Pow(D(toNumber a), b)
    static member Atan2(a : int, b : DVector) = DVector.Atan2(D(toNumber a), b)
    
    static member Log(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(log, a)
        let inline fd (a) = log a
        let inline df (cp, ap, at) = at ./ ap
        let inline r (a) = Log_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Log10(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(log10, a)
        let inline fd (a) = log10 a
        let inline df (cp, ap : DVector, at : DVector) = at ./ (ap * log10Val())
        let inline r (a) = Log10_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Exp(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(exp, a)
        let inline fd (a) = exp a
        let inline df (cp, ap, at) = at .* cp // cp = exp ap
        let inline r (a) = Exp_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Sin(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(sin, a)
        let inline fd (a) = sin a
        let inline df (cp, ap : DVector, at : DVector) = at .* cos ap
        let inline r (a) = Sin_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Cos(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(cos, a)
        let inline fd (a) = cos a
        let inline df (cp, ap : DVector, at : DVector) = -at .* sin ap
        let inline r (a) = Cos_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Tan(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(tan, a)
        let inline fd (a) = tan a
        
        let inline df (cp, ap : DVector, at : DVector) = 
            let cosa = cos ap
            at ./ (cosa .* cosa)
        
        let inline r (a) = Tan_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member (~-) (a : DVector) = 
        let inline ff (a) = Backend(a).Mul_S_V(numberMinus1, a)
        let inline fd (a) = -a
        let inline df (cp, ap, at) = -at
        let inline r (a) = Neg_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Sqrt(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(sqrt, a)
        let inline fd (a) = sqrt a
        let inline df (cp : DVector, ap : DVector, at : DVector) = at ./ (D number2 * cp) // cp = sqrt ap
        let inline r (a) = Sqrt_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Sinh(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(sinh, a)
        let inline fd (a) = sinh a
        let inline df (cp : DVector, ap : DVector, at : DVector) = at .* cosh ap
        let inline r (a) = Sinh_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Cosh(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(cosh, a)
        let inline fd (a) = cosh a
        let inline df (cp : DVector, ap : DVector, at : DVector) = at .* sinh ap
        let inline r (a) = Cosh_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Tanh(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(tanh, a)
        let inline fd (a) = tanh a
        
        let inline df (cp : DVector, ap : DVector, at : DVector) = 
            let cosha = cosh ap
            at ./ (cosha .* cosha)
        
        let inline r (a) = Tanh_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Asin(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(asin, a)
        let inline fd (a) = asin a
        let inline df (cp : DVector, ap : DVector, at : DVector) = at ./ sqrt (D number1 - (ap .* ap))
        let inline r (a) = Asin_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Acos(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(acos, a)
        let inline fd (a) = acos a
        let inline df (cp : DVector, ap : DVector, at : DVector) = -at ./ sqrt (D number1 - (ap .* ap))
        let inline r (a) = Acos_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Atan(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(atan, a)
        let inline fd (a) = atan a
        let inline df (cp : DVector, ap : DVector, at : DVector) = at ./ sqrt (D number1 + (ap .* ap))
        let inline r (a) = Atan_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Abs(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(abs, a)
        let inline fd (a) = abs a
        let inline df (cp, ap, at) = at .* (DVector.Sign ap)
        let inline r (a) = Abs_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Sign(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(signummod, a)
        let inline fd (a) = DVector.Sign a
        let inline df (cp, ap, at) = DVector.ZeroN a.Length
        let inline r (a) = Sign_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Floor(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(floor, a)
        let inline fd (a) = floor a
        let inline df (cp, ap, at) = DVector.ZeroN a.Length
        let inline r (a) = Floor_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Ceiling(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(ceil, a)
        let inline fd (a) = ceil a
        let inline df (cp, ap, at) = DVector.ZeroN a.Length
        let inline r (a) = Ceil_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Round(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(round, a)
        let inline fd (a) = round a
        let inline df (cp, ap, at) = DVector.ZeroN a.Length
        let inline r (a) = Round_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    /// L1 norm of vector `a`
    static member L1Norm(a : DVector) = 
        let inline ff (a) = Backend(a).L1Norm_V(a)
        let inline fd (a) = DVector.L1Norm(a)
        let inline df (cp, ap, at) = at * DVector.Sign(ap)
        let inline r (a) = L1Norm_DV(a)
        DVector.Op_DV_D(a, ff, fd, df, r)
    
    /// Squared L2 norm of vector `a`
    static member L2NormSq(a : DVector) = 
        let inline ff (a) = 
            let l2norm = Backend(a).L2Norm_V(a)
            l2norm * l2norm
        
        let inline fd (a) = DVector.L2NormSq(a)
        let inline df (cp, ap, at) = (D number2) * (ap * at)
        let inline r (a) = L2NormSq_DV(a)
        DVector.Op_DV_D(a, ff, fd, df, r)
    
    /// L2 norm of vector `a`
    static member L2Norm(a : DVector) = 
        let inline ff (a) = Backend(a).L2Norm_V(a)
        let inline fd (a) = DVector.L2Norm(a)
        let inline df (cp, ap, at) = (ap * at) / cp // cp = DV.L2Norm(ap)
        let inline r (a) = L2Norm_DV(a)
        DVector.Op_DV_D(a, ff, fd, df, r)
    
    /// Sum of the elements of vector `a`
    static member Sum(a : DVector) = 
        let inline ff (a) = Backend(a).Sum_V(a)
        let inline fd (a) = DVector.Sum(a)
        let inline df (cp, ap, at) = DVector.Sum(at)
        let inline r (a) = Sum_DV(a)
        DVector.Op_DV_D(a, ff, fd, df, r)
    
    /// Append vector `b` to vector `a`
    static member Append(a : DVector, b : DVector) = 
        if a.Length = 0 then b
        elif b.Length = 0 then a
        else 
            let inline ff (a : IDataBuffer, b : IDataBuffer) = 
                NativeDataBuffer<number>(Array.append a.SubData b.SubData)
            let inline fd (a, b) = DVector.Append(a, b)
            let inline df_da (cp, ap, at) = DVector.Append(at, DVector.ZeroN b.Length)
            let inline df_db (cp, bp, bt) = DVector.Append(DVector.ZeroN a.Length, bt)
            let inline df_dab (cp, ap, at, bp, bt) = DVector.Append(at, bt)
            let inline r_d_d (a, b) = Append_DV_DV(a, b)
            let inline r_d_c (a, b) = Append_DV_DVCons(a)
            let inline r_c_d (a, b) = Append_DVCons_DV(b)
            DVector.Op_DV_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member ReshapeToDM(m : int, a : DVector) = 
        let inline ff (a) = Backend(a).ReshapeCopy_V_MRows(m, a)
        let inline fd (a) = DVector.ReshapeToDM(m, a)
        let inline df (cp, ap, at) = DVector.ReshapeToDM(m, at)
        let inline r (a) = ReshapeCopy_DV_DM(a)
        DVector.Op_DV_DM(a, ff, fd, df, r)
    
    static member ReLU(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V(max number0, a)
        let inline fd (a) = DVector.ReLU(a)
        let inline df (cp, ap, at) = at .* ((number1 + DVector.Sign(ap)) / number2)
        let inline r (a) = ReLU_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member Sigmoid(a : DVector) = 
        let inline ff (a) = Backend(a).Map_F_V((fun v -> number1 / (number1 + exp -v)), a)
        let inline fd (a) = DVector.Sigmoid(a)
        let inline df (cp : DVector, ap, at) = at .* cp .* (number1 - cp)
        let inline r (a) = Sigmoid_DV(a)
        DVector.Op_DV_DV(a, ff, fd, df, r)
    
    static member SoftPlus(a : DVector) = log (number1 + exp a)
    static member SoftSign(a : DVector) = a ./ (number1 + abs a)
    static member Mean(a : DVector) = DVector.Sum(a) / a.Length
    
    static member Variance(a : DVector) = 
        let a' = a - DVector.Mean(a)
        DVector.Sum(a' .* a') / (a.Length - 1)
    
    static member StandardDev(a : DVector) = DVector.Variance(a) |> sqrt
    
    static member Standardize(a : DVector) = 
        let sd = DVector.StandardDev(a)
        if sd = D number0 then a * (D number0)
        else (a - DVector.Mean(a)) / DVector.StandardDev(a)
    
    static member Normalize(a : DVector) = 
        let min = DVector.Min(a)
        let range = DVector.Max(a) - min
        if range = D number0 then a * (D number0)
        else (a - min) / range
    
    static member Max(a : DVector, b : DVector) = ((a + b) + abs (b - a)) / number2
    static member Max(a : DVector, b : DNumber) = ((a + b) + abs (b - a)) / number2
    static member Max(a : DNumber, b : DVector) = ((a + b) + abs (b - a)) / number2
    static member Min(a : DVector, b : DVector) = ((a + b) - abs (a - b)) / number2
    static member Min(a : DVector, b : DNumber) = ((a + b) - abs (a - b)) / number2
    static member Min(a : DNumber, b : DVector) = ((a + b) - abs (a - b)) / number2
    
    /// Index of the maximum element of vector `a`
    static member MaxIndex(a : DVector) = 
        let a' = DVector.op_Explicit (a)
        let mutable maxi = 0
        let mutable maxv = a'.[0]
        for i = 0 to a'.Length - 1 do
            if a'.[i] > maxv then 
                maxi <- i
                maxv <- a'.[i]
        maxi
    
    static member Max(a : DVector) = a.[DVector.MaxIndex(a)]
    
    /// Index of the minimum element of vector `b`
    static member MinIndex(a : DVector) = 
        let a' = DVector.op_Explicit (a)
        let mutable mini = 0
        let mutable minv = a'.[0]
        for i = 0 to a'.Length - 1 do
            if a'.[i] < minv then 
                mini <- i
                minv <- a'.[i]
        mini
    
    static member Min(a : DVector) = a.[DVector.MinIndex(a)]
    
    static member SoftMax(a : DVector) = 
        let a' = a - DVector.Max(a)
        let e = exp a'
        e / DVector.Sum(e)
    
    member d.Visualize() = 
        let (d' : number []) = 
            (((VisualizationContrast()) * (DVector.Normalize(d.P) - number0_5)) + number0_5) |> DVector.op_Explicit
        let sb = System.Text.StringBuilder()
        match d with
        | DV(_) -> sb.AppendLine(sprintf "DV : %i" d.Length) |> ignore
        | DVF(_) -> sb.AppendLine(sprintf "DVF: %i" d.Length) |> ignore
        | DVR(_) -> sb.AppendLine(sprintf "DVR: %i" d.Length) |> ignore
        let palette = GlobalConfig.GrayscalePalette
        let palettel = palette.Length
        let palettelf = toNumber palettel
        for i = 0 to d.Length - 1 do
            let c = int (d'.[i] * palettelf) - 1
            let c = max 0 c
            let c = min (palettel - 1) c
            sb.Append(palette.[c]) |> ignore
        sb.ToString()

/// Matrix numeric type keeping dual numbers for forward mode and adjoints and tapes for reverse mode AD, with nesting capability, using tags to avoid perturbation confusion
and DNDArray = 
    | DM of ShapedDataBufferView<number> // Primal
    | DMF of DNDArray * DNDArray * uint32 // Primal, tangent, tag
    | DMR of DNDArray * DNDArray ref * TraceOp * uint32 ref * uint32 // Primal, adjoint, parent operation, fan-out counter, tag
    
    /// Primal value of this DM
    member d.P = 
        match d with
        | DM(_) -> d
        | DMF(ap, _, _) -> ap
        | DMR(ap, _, _, _, _) -> ap
    
    /// Deepest primal value of this DM
    member d.PD = 
        let rec prec x = 
            match x with
            | DM(_) -> x
            | DMF(xp, _, _) -> prec xp
            | DMR(xp, _, _, _, _) -> prec xp
        prec d
    
    /// Tangent value of this DM
    member d.T = 
        match d with
        | DM(_) -> DNDArray.ZeroMN d.Rows d.Cols (Backend(d))
        | DMF(_, at, _) -> at
        | DMR(_, _, _, _, _) -> failwith "Cannot get tangent value of DMR."
    
    /// Adjoint value of this DM
    member d.A 
        with get () = 
            match d with
            | DM(_) -> DNDArray.ZeroMN d.Rows d.Cols (Backend(d))
            | DMF(_, _, _) -> failwith "Cannot get adjoint value of DMF."
            | DMR(_, a, _, _, _) -> !a
        and set (v) = 
            match d with
            | DM(_) -> ()
            | DMF(_, _, _) -> failwith "Cannot set adjoint value of DMF."
            | DMR(_, a, _, _, _) -> a := v
    
    /// Fan-out value of this DM
    member d.F 
        with get () = 
            match d with
            | DM(_) -> failwith "Cannot get fan-out value of DM."
            | DMF(_, _, _) -> failwith "Cannot get fan-out value of DMF."
            | DMR(_, _, _, f, _) -> !f
        and set (v) = 
            match d with
            | DM(_) -> failwith "Cannot set fan-out value of DM."
            | DMF(_, _, _) -> failwith "Cannot set fan-out value of DMF."
            | DMR(_, _, _, f, _) -> f := v
    
    member d.Buffer = 
        let rec prec x = 
            match x with
            | DM(p) -> p
            | DMF(xp, _, _) -> prec xp
            | DMR(xp, _, _, _, _) -> prec xp
        
        let data = (prec d)
        data

    member d.GetForward(t : DNDArray, i : uint32) = DMF(d, t, i)
    member d.GetReverse(i : uint32) = DMR(d, ref (DNDArray.ZeroMN d.Rows d.Cols (Backend(d))), Noop, ref 0u, i)
    
    member d.DeepCopy() = 
        match d with
        | DM(ap) -> DM(ap)
        | DMF(ap, at, ai) -> DMF(ap.DeepCopy(), at.DeepCopy(), ai)
        | DMR(ap, aa, at, af, ai) -> DMR(ap.DeepCopy(), ref ((!aa).DeepCopy()), at, ref (!af), ai)
    
    member d.Length = 
        match d with
        | DM(ap) -> ap.Length
        | DMF(ap, _, _) -> ap.Length
        | DMR(ap, _, _, _, _) -> ap.Length
    
    member d.Rows = 
        match d with
        | DM(ap) -> int32 ap.Rows
        | DMF(ap, _, _) -> int32 ap.Rows
        | DMR(ap, _, _, _, _) -> int32 ap.Rows
    
    member d.Cols = 
        match d with
        | DM(ap) -> int32 ap.Cols
        | DMF(ap, _, _) -> int32 ap.Cols
        | DMR(ap, _, _, _, _) -> int32 ap.Cols
    
    member d.Item 
        with get (i, j) = 
            match d with
            | DM(ap) -> D(ap.[i, j])
            | DMF(ap, at, ai) -> DF(ap.[i, j], at.[i, j], ai)
            | DMR(ap, _, _, _, ai) -> DR(ap.[i, j], ref (D number0), Item_DM(d, i, j), ref 0u, ai)
    
    member d.FlatItem 
        with get (i) = 
            match d with
            | DM(ap) -> D(ap.FlatItem(i))
            | DMF(ap, at, ai) -> DF(ap.FlatItem(i), at.FlatItem(i), ai)
            | DMR(ap, _, _, _, ai) -> 
                DR(ap.FlatItem(i), ref (D number0), Item_DM(d, i / d.Rows, i % d.Rows), ref 0u, ai)
    
    override d.ToString() = 
        let sb = System.Text.StringBuilder()
        match d with
        | DM(_) -> sb.AppendLine(sprintf "DM : %i x %i" d.Rows d.Cols) |> ignore
        | DMF(_) -> sb.AppendLine(sprintf "DMF: %i x %i" d.Rows d.Cols) |> ignore
        | DMR(_) -> sb.AppendLine(sprintf "DMR: %i x %i" d.Rows d.Cols) |> ignore
        for i = 0 to d.Rows - 1 do
            for j = 0 to d.Cols - 1 do
                sb.Append(sprintf "%A " (d.Item(i, j))) |> ignore
            if i < d.Rows - 1 then sb.AppendLine() |> ignore
        sb.ToString()
    
    static member Zero = DM(ShapedDataBufferView(NativeDataBuffer<number>(Array.empty), int64 0))
    static member ZeroMN m n (b : Backend<number>) = 
        DM(ShapedDataBufferView(b.CreateDataBuffer(Array.create (m * n) number0), int64 m, int64 n))
    
    static member OfRows(s : seq<DVector>) = 
        // TODO: check to ensure that all elements in the array are of the same type (D, DF, or DR) and have the same nesting tag
        match Seq.head s with
        | DV(_) -> 
            DNDArray.OfNumberArray(Seq.length s, 
                                   s
                                   |> Seq.map DVector.op_Explicit
                                   |> Seq.concat
                                   |> Seq.toArray, 
                                   Backend(s))
        | DVF(_, _, ai) -> 
            let ap = s |> Seq.map (fun x -> x.P)
            let at = s |> Seq.map (fun x -> x.T)
            DMF(DNDArray.OfRows(ap), DNDArray.OfRows(at), ai)
        | DVR(_, _, _, _, ai) -> 
            let ap = s |> Seq.map (fun x -> x.P)
            let cp = DNDArray.OfRows(ap)
            DMR
                (cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(ap))), Make_DMRows_ofDVs(s |> Seq.toArray), ref 0u, 
                 ai)
    
    // Creates a matrix with `m` rows from array `a`, filling columns from left to right and rows from top to bottom. The number of columns will be deduced from `m` and the length of `a`. The length of `a` must be an integer multiple of `m`.
    static member OfDNumberArray(m : int, a : DNumber [], backend : Backend<number>) = 
        let n = a.Length / m
        let size = m * n
        let data = Array.create size number0
        for i = 0 to a.Length - 1 do
            data.[i] <- float32 a.[i] //type dependent operation #TDO
        match a.[0] with
        | D(_) -> DM(ShapedDataBufferView(backend.CreateDataBuffer(data), int64 m, int64 n))
        | DF(_, _, ai) -> 
            DMF
                (DNDArray.OfDNumberArray(m, a |> Array.map (fun x -> x.P), backend), 
                 DNDArray.OfDNumberArray(m, a |> Array.map (fun x -> x.T), backend), ai)
        | DR(_, _, _, _, ai) -> 
            let cp = DNDArray.OfDNumberArray(m, a |> Array.map (fun x -> x.P), backend)
            DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), Make_DM_ofDs(a), ref 0u, ai)
    
    static member OfNumberArray(m : int, a : number [], backend : Backend<number>) = 
        let n = a.Length / m
        let size = m * n
        let mutable result = a
        if (m % a.Length <> 0) then 
            let result = Array.create size number0
            for i = 0 to a.Length - 1 do
                result.[i] <- a.[i]
        DM(ShapedDataBufferView(backend.CreateDataBuffer(result), int64 m, int64 n))
    
    static member inline Op_DM_DM(a, ff, fd, df, r) = 
        match a with
        | DM(ap) -> DM(ff (ap))
        | DMF(ap, at, ai) -> 
            let cp = fd (ap)
            DMF(cp, df (cp, ap, at), ai)
        | DMR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r (a), ref 0u, ai)
    
    static member inline Op_DM_DV(a, ff, fd, df, r) = 
        match a with
        | DM(ap) -> DV(ff (ap))
        | DMF(ap, at, ai) -> 
            let cp = fd (ap)
            DVF(cp, df (cp, ap, at), ai)
        | DMR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DVR(cp, ref (DVector.ZeroN cp.Length), r (a), ref 0u, ai)
    
    static member inline Op_DM_D(a, ff, fd, df, r) = 
        match a with
        | DM(ap) -> D(ff (ap))
        | DMF(ap, at, ai) -> 
            let cp = fd (ap)
            DF(cp, df (cp, ap, at), ai)
        | DMR(ap, _, _, _, ai) -> 
            let cp = fd (ap)
            DR(cp, ref (D number0), r (a), ref 0u, ai)
    
    static member inline Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DM(ap) -> 
            match b with
            | DM(bp) -> DM(ff (ap, bp))
            | DMF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DMR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DMF(ap, at, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DMR(ap, _, _, _, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DM(ap) -> 
            match b with
            | D(bp) -> DM(ff (ap, bp))
            | DF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DMF(ap, at, ai) -> 
            match b with
            | D(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DMR(ap, _, _, _, ai) -> 
            match b with
            | D(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | D(ap) -> 
            match b with
            | DM(bp) -> DM(ff (ap, bp))
            | DMF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DMR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DF(ap, at, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DR(ap, _, _, _, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DM_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DM(ap) -> 
            match b with
            | DV(bp) -> DV(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DVF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi)
        | DMF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DMR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DV_DM_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | DM(bp) -> DV(ff (ap, bp))
            | DMF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DVF(cp, df_db (cp, bp, bt), bi)
            | DMR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DVF(cp, df_da (cp, ap, at), ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DVF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DVR(cp, ref (DVector.ZeroN cp.Length), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DM_DV_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DM(ap) -> 
            match b with
            | DV(bp) -> DM(ff (ap, bp))
            | DVF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DVR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DMF(ap, at, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DMR(ap, _, _, _, ai) -> 
            match b with
            | DV(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DVF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DVR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    static member inline Op_DV_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d) = 
        match a with
        | DV(ap) -> 
            match b with
            | DM(bp) -> DM(ff (ap, bp))
            | DMF(bp, bt, bi) -> 
                let cp = fd (a, bp)
                DMF(cp, df_db (cp, bp, bt), bi)
            | DMR(bp, _, _, _, bi) -> 
                let cp = fd (a, bp)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi)
        | DVF(ap, at, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMF(cp, df_da (cp, ap, at), ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMF(cp, df_dab (cp, ap, at, bp, bt), ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMF(cp, df_da (cp, ap, at), ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
        | DVR(ap, _, _, _, ai) -> 
            match b with
            | DM(_) -> 
                let cp = fd (ap, b)
                DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai)
            | DMF(bp, bt, bi) -> 
                match compare ai bi with
                | -1 -> 
                    let cp = fd (a, bp)
                    DMF(cp, df_db (cp, bp, bt), bi) // ai < bi
                | 1 -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
                | _ -> failwith "Forward and reverse AD cannot run on the same level."
            | DMR(bp, _, _, _, bi) -> 
                match compare ai bi with
                | 0 -> 
                    let cp = fd (ap, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_d (a, b), ref 0u, ai) // ai = bi
                | -1 -> 
                    let cp = fd (a, bp)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_c_d (a, b), ref 0u, bi) // ai < bi
                | _ -> 
                    let cp = fd (ap, b)
                    DMR(cp, ref (DNDArray.ZeroMN cp.Rows cp.Cols (Backend(cp))), r_d_c (a, b), ref 0u, ai) // ai > bi
    
    /// Element-wise addition of `a` and `b`
    static member (+) (a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Add_M_M(a, b)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = bt
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DM_DM(a, b)
        let inline r_d_c (a, b) = Add_DM_DMCons(a)
        let inline r_c_d (a, b) = Add_DM_DMCons(b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise subtraction of `a` and `b`
    static member (-) (a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Sub_M_M(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = -bt
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_DM_DM(a, b)
        let inline r_d_c (a, b) = Sub_DM_DMCons(a)
        let inline r_c_d (a, b) = Sub_DMCons_DM(b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Matrix product of `a` and `b`
    static member (*) (a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Mul_M_M(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DM_DM(a, b)
        let inline r_d_c (a, b) = Mul_DM_DMCons(a, b)
        let inline r_c_d (a, b) = Mul_DMCons_DM(a, b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise (Hadamard, Schur) product of `a` and `b`
    static member (.*) (a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Mul_Had_M_M(a, b)
        let inline fd (a, b) = a .* b
        let inline df_da (cp, ap, at) = at .* b
        let inline df_db (cp, bp, bt) = a .* bt
        let inline df_dab (cp, ap, at, bp, bt) = (at .* bp) + (ap .* bt)
        let inline r_d_d (a, b) = Mul_Had_DM_DM(a, b)
        let inline r_d_c (a, b) = Mul_Had_DM_DMCons(a, b)
        let inline r_c_d (a, b) = Mul_Had_DM_DMCons(b, a)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Right-multiply matrix `a` by vector `b`
    static member (*) (a : DNDArray, b : DVector) = 
        let inline ff (a, b) = Backend(a).Mul_M_V(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DM_DV(a, b)
        let inline r_d_c (a, b) = Mul_DM_DVCons(a, b)
        let inline r_c_d (a, b) = Mul_DMCons_DV(a, b)
        DNDArray.Op_DM_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Left-multiply matrix `b` by vector `a`
    static member (*) (a : DVector, b : DNDArray) = 
        let inline ff (a, b) = Backend(b).Mul_V_M(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DV_DM(a, b)
        let inline r_d_c (a, b) = Mul_DV_DMCons(a, b)
        let inline r_c_d (a, b) = Mul_DVCons_DM(a, b)
        DNDArray.Op_DV_DM_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Element-wise (Hadamard, Schur) division `a` and `b`
    static member (./) (a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Map2_F_M_M((/), a, b)
        let inline fd (a, b) = a ./ b
        let inline df_da (cp, ap, at) = at ./ b
        let inline df_db (cp, bp, bt) = -bt .* cp ./ bp // cp = ap / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt .* cp) ./ bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_Had_DM_DM(a, b)
        let inline r_d_c (a, b) = Div_Had_DM_DMCons(a, b)
        let inline r_c_d (a, b) = Div_Had_DMCons_DM(a, b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Pow(a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Map2_F_M_M((fun x y -> x ** y), a, b)
        let inline fd (a, b) = a ** b
        let inline df_da (cp, ap, at) = at .* (ap ** (b - D number1)) .* b
        let inline df_db (cp, bp, bt) = bt .* cp .* log a // cp = a ** bp
        let inline df_dab (cp, ap, at, bp, bt) = (ap ** (bp - D number1)) .* (at .* bp + ap .* bt .* log ap)
        let inline r_d_d (a, b) = Pow_DM_DM(a, b)
        let inline r_d_c (a, b) = Pow_DM_DMCons(a, b)
        let inline r_c_d (a, b) = Pow_DMCons_DM(a, b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Atan2(a : DNDArray, b : DNDArray) = 
        let inline ff (a, b) = Backend(a).Map2_F_M_M(atan2, a, b)
        let inline fd (a, b) = atan2 a b
        let inline df_da (cp, ap, at) = (at .* b) ./ ((ap .* ap) + (b .* b))
        let inline df_db (cp, bp, bt) = (-bt .* a) ./ ((a .* a) + (bp .* bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at .* bp) - (bt .* ap)) ./ ((ap .* ap) + (bp .* bp))
        let inline r_d_d (a, b) = Atan2_DM_DM(a, b)
        let inline r_d_c (a, b) = Atan2_DM_DMCons(a, b)
        let inline r_c_d (a, b) = Atan2_DMCons_DM(a, b)
        DNDArray.Op_DM_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (*) (a : DNDArray, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Mul_S_M(b, a)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DM_D(a, b)
        let inline r_d_c (a, b) = Mul_DM_DCons(a, b)
        let inline r_c_d (a, b) = Mul_DMCons_D(a, b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (*) (a : DNumber, b : DNDArray) = 
        let inline ff (a, b) = Backend(b).Mul_S_M(a, b)
        let inline fd (a, b) = a * b
        let inline df_da (cp, ap, at) = at * b
        let inline df_db (cp, bp, bt) = a * bt
        let inline df_dab (cp, ap, at, bp, bt) = (at * bp) + (ap * bt)
        let inline r_d_d (a, b) = Mul_DM_D(b, a)
        let inline r_d_c (a, b) = Mul_DM_DCons(b, a)
        let inline r_c_d (a, b) = Mul_DMCons_D(b, a)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (/) (a : DNDArray, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Mul_S_M(number1 / b, a)
        let inline fd (a, b) = a / b
        let inline df_da (cp, ap, at) = at / b
        let inline df_db (cp, bp, bt) = -bt * cp / bp // cp = a / bp
        let inline df_dab (cp, ap, at, bp, bt) = (at - bt * cp) / bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_DM_D(a, b)
        let inline r_d_c (a, b) = Div_DM_DCons(a, b)
        let inline r_c_d (a, b) = Div_DMCons_D(a, b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (/) (a : DNumber, b : DNDArray) = 
        let inline ff (a, b) = Backend(b).Map_F_M((fun v -> a / v), b)
        let inline fd (a, b) = a / b
        let inline df_da (cp, ap, at) = at / b
        let inline df_db (cp, bp, bt) = -bt .* (cp ./ bp) // cp = a / bp
        let inline df_dab (cp : DNDArray, ap : DNumber, at : DNumber, bp : DNDArray, bt : DNDArray) = 
            (at - bt .* cp) ./ bp // cp = ap / bp
        let inline r_d_d (a, b) = Div_D_DM(a, b)
        let inline r_d_c (a, b) = Div_D_DMCons(a, b)
        let inline r_c_d (a, b) = Div_DCons_DM(a, b)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (+) (a : DNDArray, b : DNumber) = 
        let backend = Backend(a)
        let inline ff (a, b) = backend.Add_S_M(b, a)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DNDArray.OfDNumberArray(a.Rows, Array.create (a.Rows * a.Cols) bt, backend)
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DM_D(a, b)
        let inline r_d_c (a, b) = Add_DM_DCons(a)
        let inline r_c_d (a, b) = Add_DMCons_D(b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (+) (a : DNumber, b : DNDArray) = 
        let backend = Backend(b)
        let inline ff (a, b) = backend.Add_S_M(a, b)
        let inline fd (a, b) = a + b
        let inline df_da (cp, ap, at) = DNDArray.OfDNumberArray(b.Rows, Array.create (b.Rows * b.Cols) at, backend)
        let inline df_db (cp, bp, bt) = bt
        let inline df_dab (cp, ap, at, bp, bt) = at + bt
        let inline r_d_d (a, b) = Add_DM_D(b, a)
        let inline r_d_c (a, b) = Add_DMCons_D(a)
        let inline r_c_d (a, b) = Add_DM_DCons(b)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (-) (a : DNDArray, b : DNumber) = 
        let backend = Backend(a)
        let inline ff (a, b) = Backend(a).Sub_M_S(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DNDArray.OfDNumberArray(a.Rows, Array.create (a.Rows * a.Cols) -bt, backend)
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_DM_D(a, b)
        let inline r_d_c (a, b) = Sub_DM_DCons(a)
        let inline r_c_d (a, b) = Sub_DMCons_D(b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member (-) (a : DNumber, b : DNDArray) = 
        let backend = Backend(b)
        let inline ff (a, b) = backend.Sub_S_M(a, b)
        let inline fd (a, b) = a - b
        let inline df_da (cp, ap, at) = DNDArray.OfDNumberArray(b.Rows, Array.create (b.Rows * b.Cols) at, backend)
        let inline df_db (cp, bp, bt) = -bt
        let inline df_dab (cp, ap, at, bp, bt) = at - bt
        let inline r_d_d (a, b) = Sub_D_DM(a, b)
        let inline r_d_c (a, b) = Sub_D_DMCons(a)
        let inline r_c_d (a, b) = Sub_DCons_DM(b)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Pow(a : DNDArray, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Map_F_M((fun v -> v ** b), a)
        let inline fd (a, b) = a ** b
        let inline df_da (cp, ap : DNDArray, at : DNDArray) = at .* (ap ** (b - D number1)) * b
        let inline df_db (cp, bp, bt) = bt * cp .* log a // cp = a ** bp
        let inline df_dab (cp, ap : DNDArray, at : DNDArray, bp : DNumber, bt : DNumber) = 
            (ap ** (bp - D number1)) .* ((at * bp) + (ap * bt .* log ap))
        let inline r_d_d (a, b) = Pow_DM_D(a, b)
        let inline r_d_c (a, b) = Pow_DM_DCons(a, b)
        let inline r_c_d (a, b) = Pow_DMCons_D(a, b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Pow(a : DNumber, b : DNDArray) = 
        let inline ff (a, b) = Backend(b).Map_F_M((fun v -> a ** v), b)
        let inline fd (a : DNumber, b : DNDArray) = DNDArray.Pow(a, b)
        let inline df_da (cp, ap : DNumber, at : DNumber) = at * (DNDArray.Pow(ap, b - D number1)) .* b
        let inline df_db (cp, bp, bt) = bt .* cp * log a // cp = a ** bp
        let inline df_dab (cp, ap : DNumber, at : DNumber, bp : DNDArray, bt : DNDArray) = 
            (DNDArray.Pow(ap, bp - D number1)) .* ((at * bp) + (ap * bt * log ap))
        let inline r_d_d (a, b) = Pow_D_DM(a, b)
        let inline r_d_c (a, b) = Pow_D_DMCons(a, b)
        let inline r_c_d (a, b) = Pow_DCons_DM(a, b)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Atan2(a : DNDArray, b : DNumber) = 
        let inline ff (a, b) = Backend(a).Map_F_M((fun v -> atan2 v b), a)
        let inline fd (a : DNDArray, b : DNumber) = DNDArray.Atan2(a, b)
        let inline df_da (cp, ap, at) = (at * b) ./ ((ap .* ap) + (b * b))
        let inline df_db (cp, bp, bt) = (-bt * a) ./ ((a .* a) + (bp * bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at * bp) - (bt * ap)) ./ ((ap .* ap) + (bp * bp))
        let inline r_d_d (a, b) = Atan2_DM_D(a, b)
        let inline r_d_c (a, b) = Atan2_DM_DCons(a, b)
        let inline r_c_d (a, b) = Atan2_DMCons_D(a, b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member Atan2(a : DNumber, b : DNDArray) = 
        let inline ff (a, b) = Backend(b).Map_F_M((fun v -> atan2 a v), b)
        let inline fd (a : DNumber, b : DNDArray) = DNDArray.Atan2(a, b)
        let inline df_da (cp, ap, at) = (at * b) ./ ((ap * ap) + (b .* b))
        let inline df_db (cp, bp, bt) = (-bt * a) ./ ((a * a) + (bp .* bp))
        let inline df_dab (cp, ap, at, bp, bt) = ((at * bp) - (bt * ap)) ./ ((ap * ap) + (bp .* bp))
        let inline r_d_d (a, b) = Atan2_D_DM(a, b)
        let inline r_d_c (a, b) = Atan2_D_DMCons(a, b)
        let inline r_c_d (a, b) = Atan2_DCons_DM(a, b)
        DNDArray.Op_D_DM_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    // DM - number binary operations
    static member (+) (a : DNDArray, b : number) = a + D b
    static member (-) (a : DNDArray, b : number) = a - D b
    static member (*) (a : DNDArray, b : number) = a * D b
    static member (/) (a : DNDArray, b : number) = a / D b
    static member Pow(a : DNDArray, b : number) = a ** D b
    static member Atan2(a : DNDArray, b : number) = DNDArray.Atan2(a, D b)
    // number - DM binary operations
    static member (+) (a : number, b : DNDArray) = (D a) + b
    static member (-) (a : number, b : DNDArray) = (D a) - b
    static member (*) (a : number, b : DNDArray) = (D a) * b
    static member (/) (a : number, b : DNDArray) = (D a) / b
    static member Pow(a : number, b : DNDArray) = DNDArray.Pow(D a, b)
    static member Atan2(a : number, b : DNDArray) = DNDArray.Atan2(D a, b)
    // DM - int binary operations
    static member (+) (a : DNDArray, b : int) = a + D(toNumber b)
    static member (-) (a : DNDArray, b : int) = a - D(toNumber b)
    static member (*) (a : DNDArray, b : int) = a * D(toNumber b)
    static member (/) (a : DNDArray, b : int) = a / D(toNumber b)
    static member Pow(a : DNDArray, b : int) = a ** D(toNumber b)
    static member Atan2(a : DNDArray, b : int) = DNDArray.Atan2(a, D(toNumber b))
    // int - DM binary operations
    static member (+) (a : int, b : DNDArray) = (D(toNumber a)) + b
    static member (-) (a : int, b : DNDArray) = (D(toNumber a)) - b
    static member (*) (a : int, b : DNDArray) = (D(toNumber a)) * b
    static member (/) (a : int, b : DNDArray) = (D(toNumber a)) / b
    static member Pow(a : int, b : DNDArray) = DNDArray.Pow(D(toNumber a), b)
    static member Atan2(a : int, b : DNDArray) = DNDArray.Atan2(D(toNumber a), b)
    
    static member Log(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(log, a)
        let inline fd (a) = log a
        let inline df (cp, ap, at) = at ./ ap
        let inline r (a) = Log_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Log10(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(log10, a)
        let inline fd (a) = log10 a
        let inline df (cp, ap : DNDArray, at : DNDArray) = at ./ (ap * log10Val())
        let inline r (a) = Log10_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Exp(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(exp, a)
        let inline fd (a) = exp a
        let inline df (cp, ap, at) = at .* cp // cp = exp ap
        let inline r (a) = Exp_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Sin(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(sin, a)
        let inline fd (a) = sin a
        let inline df (cp, ap : DNDArray, at : DNDArray) = at .* cos ap
        let inline r (a) = Sin_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Cos(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(cos, a)
        let inline fd (a) = cos a
        let inline df (cp, ap : DNDArray, at : DNDArray) = -at .* sin ap
        let inline r (a) = Cos_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Tan(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(tan, a)
        let inline fd (a) = tan a
        
        let inline df (cp, ap : DNDArray, at : DNDArray) = 
            let cosa = cos ap
            at ./ (cosa .* cosa)
        
        let inline r (a) = Tan_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member (~-) (a : DNDArray) = 
        let inline ff (a) = Backend(a).Mul_S_M(numberMinus1, a)
        let inline fd (a) = -a
        let inline df (cp, ap, at) = -at
        let inline r (a) = Neg_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Sqrt(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(sqrt, a)
        let inline fd (a) = sqrt a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = at ./ (D number2 * cp) // cp = sqrt ap
        let inline r (a) = Sqrt_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Sinh(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(sinh, a)
        let inline fd (a) = sinh a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = at .* cosh ap
        let inline r (a) = Sinh_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Cosh(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(cosh, a)
        let inline fd (a) = cosh a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = at .* sinh ap
        let inline r (a) = Cosh_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Tanh(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(tanh, a)
        let inline fd (a) = tanh a
        
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = 
            let cosha = cosh ap
            at ./ (cosha .* cosha)
        
        let inline r (a) = Tanh_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Asin(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(asin, a)
        let inline fd (a) = asin a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = at ./ sqrt (D number1 - (ap .* ap))
        let inline r (a) = Asin_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Acos(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(acos, a)
        let inline fd (a) = acos a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = -at ./ sqrt (D number1 - (ap .* ap))
        let inline r (a) = Acos_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Atan(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(atan, a)
        let inline fd (a) = atan a
        let inline df (cp : DNDArray, ap : DNDArray, at : DNDArray) = at ./ sqrt (D number1 + (ap .* ap))
        let inline r (a) = Atan_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Abs(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(abs, a)
        let inline fd (a) = abs a
        let inline df (cp, ap, at) = at .* (DNDArray.Sign ap)
        let inline r (a) = Abs_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Sign(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(signummod, a)
        let inline fd (a) = DNDArray.Sign a
        let inline df (cp, ap, at) = DNDArray.ZeroMN a.Rows a.Cols (Backend(cp))
        let inline r (a) = Sign_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Floor(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(floor, a)
        let inline fd (a) = floor a
        let inline df (cp, ap, at) = DNDArray.ZeroMN a.Rows a.Cols (Backend(cp))
        let inline r (a) = Floor_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Ceiling(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(ceil, a)
        let inline fd (a) = ceil a
        let inline df (cp, ap, at) = DNDArray.ZeroMN a.Rows a.Cols (Backend(cp))
        let inline r (a) = Ceil_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Round(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(round, a)
        let inline fd (a) = round a
        let inline df (cp, ap, at) = DNDArray.ZeroMN a.Rows a.Cols (Backend(cp))
        let inline r (a) = Round_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    /// Transpose of matrix `a`
    static member Transpose(a : DNDArray) = 
        let inline ff (a) = Backend(a).Transpose_M(a)
        let inline fd (a) = DNDArray.Transpose(a)
        let inline df (cp, ap, at) = DNDArray.Transpose(at)
        let inline r (a) = Transpose_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    /// Diagonal of matrix `a`
    static member Diagonal(a : DNDArray) = 
        let inline ff (a) = Backend(a).Diagonal_M(a)
        let inline fd (a) = DNDArray.Diagonal(a)
        let inline df (cp, ap, at) = DNDArray.Diagonal(at)
        let inline r (a) = Diagonal_DM(a)
        DNDArray.Op_DM_DV(a, ff, fd, df, r)
    
    /// Trace of matrix `a`
    static member Trace(a : DNDArray) = DVector.Sum(DNDArray.Diagonal(a))
    
    /// Sum of the entries of matrix `a`
    static member Sum(a : DNDArray) = 
        let inline ff (a : ShapedDataBufferView<number>) = Backend(a).Sum_M(a.DataBuffer)
        let inline fd (a) = DNDArray.Sum(a)
        let inline df (cp, ap, at) = DNDArray.Sum(at)
        let inline r (a) = Sum_DM(a)
        DNDArray.Op_DM_D(a, ff, fd, df, r)
    
    /// Solve a system of linear equations Ax = b, where the coefficient matrix `a` has general form
    static member Solve(a : DNDArray, b : DVector) = 
        let inline ff (a, b) = 
            match Backend(a).Solve_M_V(a, b) with
            | Some(x) -> x
            | _ -> ErrorMessages.InvalidArgSolve()
        
        let inline fd (a, b) = DNDArray.Solve(a, b)
        let inline df_da (cp, ap, at) = DNDArray.Solve(ap, -at * cp) // cp = DM.Solve(ap, b)
        let inline df_db (cp, bp, bt) = DNDArray.Solve(a, bt)
        let inline df_dab (cp, ap, at, bp, bt) = DNDArray.Solve(ap, bt - at * cp) // cp = DM.Solve(ap, bp)
        let inline r_d_d (a, b) = Solve_DM_DV(a, b)
        let inline r_d_c (a, b) = Solve_DM_DVCons(a, b)
        let inline r_c_d (a, b) = Solve_DMCons_DV(a, b)
        DNDArray.Op_DM_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Solve a system of linear equations Ax = b, where the coefficient matrix `a` is symmetric
    static member SolveSymmetric(a : DNDArray, b : DVector) = 
        let inline ff (a, b) = 
            match Backend(a).SolveSymmetric_M_V(a, b) with
            | Some(x) -> x
            | _ -> ErrorMessages.InvalidArgSolve()
        
        let inline fd (a, b) = DNDArray.SolveSymmetric(a, b)
        let inline df_da (cp, ap, at) = DNDArray.SolveSymmetric(ap, -at * cp) // cp = DM.Solve(ap, b)
        let inline df_db (cp, bp, bt) = DNDArray.SolveSymmetric(a, bt)
        let inline df_dab (cp, ap, at, bp, bt) = DNDArray.SolveSymmetric(ap, bt - at * cp) // cp = DM.Solve(ap, bp)
        let inline r_d_d (a, b) = Solve_DM_DV(a, b)
        let inline r_d_c (a, b) = Solve_DM_DVCons(a, b)
        let inline r_c_d (a, b) = Solve_DMCons_DV(a, b)
        DNDArray.Op_DM_DV_DV(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add scalar `b` to matrix `a` at row `i` and column `j`
    static member AddItem(a : DNDArray, i : int, j : int, b : DNumber) = 
        let inline ff (a : ShapedDataBufferView<number>, b : number) = 
            let aa = a.DeepCopy()
            aa.[i, j] <- b
            aa
        
        let inline fd (a, b) = DNDArray.AddItem(a, i, j, b)
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DNDArray.AddItem(DNDArray.ZeroMN a.Rows a.Cols (Backend(a)), i, j, bt)
        let inline df_dab (cp, ap, at, bp, bt) = DNDArray.AddItem(at, i, j, bt)
        let inline r_d_d (a, b) = AddItem_DM_D(a, i, j, b)
        let inline r_d_c (a, b) = AddItem_DM_DCons(a)
        let inline r_c_d (a, b) = AddItem_DMCons_D(i, j, b)
        DNDArray.Op_DM_D_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    /// Add the elements of vector `b` to the diagonal elements of matrix `a`
    static member AddDiagonal(a : DNDArray, b : DVector) = 
        let inline ff (a : ShapedDataBufferView<number>, b : IDataBuffer) = 
            let aa = a.DeepCopy()
            let n = min (a.Rows) (a.Cols) |> min b.Length
            for i = 0 to n - 1 do
                aa.[i, i] <- aa.[i, i] + b.SubData.[i]
            aa
        
        let inline fd (a, b) = DNDArray.AddDiagonal(a, b)
        let inline df_da (cp, ap, at) = at
        let inline df_db (cp, bp, bt) = DNDArray.AddDiagonal(DNDArray.ZeroMN a.Rows a.Cols (Backend(a)), bt)
        let inline df_dab (cp, ap, at, bp, bt) = DNDArray.AddDiagonal(at, bt)
        let inline r_d_d (a, b) = AddDiagonal_DM_DV(a, b)
        let inline r_d_c (a, b) = AddDiagonal_DM_DVCons(a)
        let inline r_c_d (a, b) = AddDiagonal_DMCons_DV(b)
        DNDArray.Op_DM_DV_DM(a, b, ff, fd, df_da, df_db, df_dab, r_d_d, r_d_c, r_c_d)
    
    static member ReshapeToDV(a : DNDArray) = 
        let inline ff (a) = Backend(a).ReshapeCopy_MRows_V(a)
        let inline fd (a) = DNDArray.ReshapeToDV(a)
        let inline df (cp, ap, at) = DNDArray.ReshapeToDV(at)
        let inline r (a) = ReshapeCopy_DM_DV(a)
        DNDArray.Op_DM_DV(a, ff, fd, df, r)
    
    /// Matrix inverse of `a`
    static member Inverse(a : DNDArray) = 
        let inline ff (a) = 
            match Backend(a).Inverse_M(a) with
            | Some(x) -> x
            | _ -> ErrorMessages.InvalidArgInverse()
        
        let inline fd (a) = DNDArray.Inverse(a)
        let inline df (cp, ap, at) = -cp * at * cp
        let inline r (a) = Inverse_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    /// Determinant of matrix `a`
    static member Det(a : DNDArray) = 
        let inline ff (a) = 
            match Backend(a).Det_M(a) with
            | Some(x) -> x
            | _ -> ErrorMessages.InvalidArgDet()
        
        let inline fd (a) = DNDArray.Det(a)
        let inline df (cp, ap, at) = cp * DNDArray.Trace(DNDArray.Inverse(ap) * at)
        let inline r (a) = Det_DM(a)
        DNDArray.Op_DM_D(a, ff, fd, df, r)
    
    static member ReLU(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M(max number0, a)
        let inline fd (a) = DNDArray.ReLU(a)
        let inline df (cp, ap, at) = at .* ((number1 + DNDArray.Sign(ap)) / number2)
        let inline r (a) = ReLU_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member Sigmoid(a : DNDArray) = 
        let inline ff (a) = Backend(a).Map_F_M((fun v -> number1 / (number1 + exp -v)), a)
        let inline fd (a) = DNDArray.Sigmoid(a)
        let inline df (cp : DNDArray, ap, at) = at .* cp .* (number1 - cp)
        let inline r (a) = Sigmoid_DM(a)
        DNDArray.Op_DM_DM(a, ff, fd, df, r)
    
    static member SoftPlus(a : DNDArray) = log (number1 + exp a)
    static member SoftSign(a : DNDArray) = a ./ (number1 + abs a)
    static member Mean(a : DNDArray) = DNDArray.Sum(a) / a.Length
    
    static member Variance(a : DNDArray) = 
        let a' = a - DNDArray.Mean(a)
        DNDArray.Sum(a' .* a') / (a.Length - 1)
    
    static member StandardDev(a : DNDArray) = DNDArray.Variance(a) |> sqrt
    
    static member Standardize(a : DNDArray) = 
        let sd = DNDArray.StandardDev(a)
        if sd = D number0 then a * (D number0)
        else (a - DNDArray.Mean(a)) / DNDArray.StandardDev(a)
    
    static member Normalize(a : DNDArray) = 
        let min = DNDArray.Min(a)
        let range = DNDArray.Max(a) - min
        if range = D number0 then a * (D number0)
        else (a - min) / range
    
    static member Max(a : DNDArray, b : DNDArray) = ((a + b) + abs (b - a)) / number2
    static member Max(a : DNDArray, b : DNumber) = ((a + b) + abs (b - a)) / number2
    static member Max(a : DNumber, b : DNDArray) = ((a + b) + abs (b - a)) / number2
    static member Min(a : DNDArray, b : DNDArray) = ((a + b) - abs (a - b)) / number2
    static member Min(a : DNDArray, b : DNumber) = ((a + b) - abs (a - b)) / number2
    static member Min(a : DNumber, b : DNDArray) = ((a + b) - abs (a - b)) / number2
    
    /// Index of the maximum element of matrix `a`
    static member MaxIndex(a : DNDArray) = 
        let mutable maxi = 0
        let mutable maxv = a.FlatItem(0)
        for i = 0 to a.Length do
            if (a.FlatItem(i) > maxv) then 
                do maxv <- a.FlatItem(i)
                do maxi <- i
        maxi
    
    static member Max(a : DNDArray) = 
        let maxi = DNDArray.MaxIndex(a)
        a.FlatItem(maxi)
    
    /// Index of the minimum element of matrix `a`
    static member MinIndex(a : DNDArray) = 
        let mutable mini = 0
        let mutable minv = a.FlatItem(0)
        for i = 0 to a.Length do
            if (a.FlatItem(i) < minv) then 
                do minv <- a.FlatItem(i)
                do mini <- i
        mini
    
    static member Min(a : DNDArray) = 
        let mini = DNDArray.MinIndex(a)
        a.FlatItem(mini)
    
    member d.Visualize() = 
        let (d' : DNDArray) = (((VisualizationContrast() * (DNDArray.Normalize(d.P) - number0_5)) + number0_5))
        let sb = System.Text.StringBuilder()
        match d with
        | DM(_) -> sb.AppendLine(sprintf "DM : %i x %i" d.Rows d.Cols) |> ignore
        | DMF(_) -> sb.AppendLine(sprintf "DMF: %i x %i" d.Rows d.Cols) |> ignore
        | DMR(_) -> sb.AppendLine(sprintf "DMR: %i x %i" d.Rows d.Cols) |> ignore
        let palette = GlobalConfig.GrayscalePalette
        let palettel = palette.Length
        let palettelf = toNumber palettel
        for i = 0 to d.Rows - 1 do
            for j = 0 to d.Cols - 1 do
                let c = int ((d'.Item(i, j) * palettelf) |> toNumber) - 1
                let c = max 0 c
                let c = min (palettel - 1) c
                sb.Append(palette.[c]) |> ignore
            if i < d.Rows - 1 then sb.AppendLine() |> ignore
        sb.ToString()

/// Operation types recorded in the evaluation trace
and TraceOp = 
    // Scalar-valued operations
    | Add_D_D of DNumber * DNumber
    | Add_D_DCons of DNumber
    | Sub_D_D of DNumber * DNumber
    | Sub_D_DCons of DNumber
    | Sub_DCons_D of DNumber
    | Mul_D_D of DNumber * DNumber
    | Mul_D_DCons of DNumber * DNumber
    | Div_D_D of DNumber * DNumber
    | Div_D_DCons of DNumber * DNumber
    | Div_DCons_D of DNumber * DNumber
    | Pow_D_D of DNumber * DNumber
    | Pow_D_DCons of DNumber * DNumber
    | Pow_DCons_D of DNumber * DNumber
    | Atan2_D_D of DNumber * DNumber
    | Atan2_D_DCons of DNumber * DNumber
    | Atan2_DCons_D of DNumber * DNumber
    | Log_D of DNumber
    | Log10_D of DNumber
    | Exp_D of DNumber
    | Sin_D of DNumber
    | Cos_D of DNumber
    | Tan_D of DNumber
    | Neg_D of DNumber
    | Sqrt_D of DNumber
    | Sinh_D of DNumber
    | Cosh_D of DNumber
    | Tanh_D of DNumber
    | Asin_D of DNumber
    | Acos_D of DNumber
    | Atan_D of DNumber
    | Abs_D of DNumber
    | Sign_D of DNumber
    | Floor_D of DNumber
    | Ceil_D of DNumber
    | Round_D of DNumber
    | Mul_Dot_DV_DV of DVector * DVector
    | Mul_Dot_DV_DVCons of DVector * DVector
    | Sum_DV of DVector
    | L1Norm_DV of DVector
    | L2NormSq_DV of DVector
    | L2Norm_DV of DVector
    | Item_DV of DVector * int
    | Sum_DM of DNDArray
    | Item_DM of DNDArray * int * int
    | ReLU_D of DNumber
    | Sigmoid_D of DNumber
    | LogSumExp_DV of DVector
    | FixedPoint_D of DNumber * DNumber * DNumber * DNumber
    // Vector-valued operations
    | Add_DV_DV of DVector * DVector
    | Add_DV_DVCons of DVector
    | Add_DV_D of DVector * DNumber
    | Add_DV_DCons of DVector
    | Add_DVCons_D of DNumber
    | Sub_DV_DV of DVector * DVector
    | Sub_DV_DVCons of DVector
    | Sub_DVCons_DV of DVector
    | Sub_DV_D of DVector * DNumber
    | Sub_DV_DCons of DVector
    | Sub_DVCons_D of DNumber
    | Sub_D_DV of DNumber * DVector
    | Sub_D_DVCons of DNumber
    | Sub_DCons_DV of DVector
    | Mul_Had_DV_DV of DVector * DVector
    | Mul_Had_DV_DVCons of DVector * DVector
    | Mul_DV_D of DVector * DNumber
    | Mul_DV_DCons of DVector * DNumber
    | Mul_DVCons_D of DVector * DNumber
    | Mul_DM_DV of DNDArray * DVector
    | Mul_DM_DVCons of DNDArray * DVector
    | Mul_DMCons_DV of DNDArray * DVector
    | Mul_DV_DM of DVector * DNDArray
    | Mul_DV_DMCons of DVector * DNDArray
    | Mul_DVCons_DM of DVector * DNDArray
    | Div_Had_DV_DV of DVector * DVector
    | Div_Had_DV_DVCons of DVector * DVector
    | Div_Had_DVCons_DV of DVector * DVector
    | Div_DV_D of DVector * DNumber
    | Div_DV_DCons of DVector * DNumber
    | Div_DVCons_D of DVector * DNumber
    | Div_D_DV of DNumber * DVector
    | Div_D_DVCons of DNumber * DVector
    | Div_DCons_DV of DNumber * DVector
    | Pow_DV_DV of DVector * DVector
    | Pow_DV_DVCons of DVector * DVector
    | Pow_DVCons_DV of DVector * DVector
    | Atan2_DV_DV of DVector * DVector
    | Atan2_DV_DVCons of DVector * DVector
    | Atan2_DVCons_DV of DVector * DVector
    | Pow_DV_D of DVector * DNumber
    | Pow_DV_DCons of DVector * DNumber
    | Pow_DVCons_D of DVector * DNumber
    | Pow_D_DV of DNumber * DVector
    | Pow_D_DVCons of DNumber * DVector
    | Pow_DCons_DV of DNumber * DVector
    | Atan2_DV_D of DVector * DNumber
    | Atan2_DV_DCons of DVector * DNumber
    | Atan2_DVCons_D of DVector * DNumber
    | Atan2_D_DV of DNumber * DVector
    | Atan2_D_DVCons of DNumber * DVector
    | Atan2_DCons_DV of DNumber * DVector
    | Exp_DV of DVector
    | Log_DV of DVector
    | Log10_DV of DVector
    | Sin_DV of DVector
    | Cos_DV of DVector
    | Tan_DV of DVector
    | Neg_DV of DVector
    | Sqrt_DV of DVector
    | Sinh_DV of DVector
    | Cosh_DV of DVector
    | Tanh_DV of DVector
    | Asin_DV of DVector
    | Acos_DV of DVector
    | Atan_DV of DVector
    | Abs_DV of DVector
    | Sign_DV of DVector
    | Floor_DV of DVector
    | Ceil_DV of DVector
    | Round_DV of DVector
    | Make_DV_ofDs of DNumber []
    | SliceRow_DM of DNDArray * int * int
    | SliceCol_DM of DNDArray * int * int
    | Solve_DM_DV of DNDArray * DVector
    | Solve_DM_DVCons of DNDArray * DVector
    | Solve_DMCons_DV of DNDArray * DVector
    | Append_DV_DV of DVector * DVector
    | Append_DV_DVCons of DVector
    | Append_DVCons_DV of DVector
    | Split_DV of DVector * int
    | AddItem_DV_D of DVector * int * DNumber
    | AddItem_DV_DCons of DVector
    | AddItem_DVCons_D of int * DNumber
    | AddSubVector_DV_DV of DVector * int * DVector
    | AddSubVector_DV_DVCons of DVector
    | AddSubVector_DVCons_DV of int * DVector
    | ReshapeCopy_DM_DV of DNDArray
    | Slice_DV of DVector * int
    | Diagonal_DM of DNDArray
    | ReLU_DV of DVector
    | Sigmoid_DV of DVector
    // Matrix-valued operations
    | Add_DM_DM of DNDArray * DNDArray
    | Add_DM_DMCons of DNDArray
    | Sub_DM_DM of DNDArray * DNDArray
    | Sub_DM_DMCons of DNDArray
    | Sub_DMCons_DM of DNDArray
    | Mul_DM_DM of DNDArray * DNDArray
    | Mul_DM_DMCons of DNDArray * DNDArray
    | Mul_DMCons_DM of DNDArray * DNDArray
    | Mul_Had_DM_DM of DNDArray * DNDArray
    | Mul_Had_DM_DMCons of DNDArray * DNDArray
    | Mul_DM_D of DNDArray * DNumber
    | Mul_DM_DCons of DNDArray * DNumber
    | Mul_DMCons_D of DNDArray * DNumber
    | Mul_Out_DV_DV of DVector * DVector
    | Mul_Out_DV_DVCons of DVector * DVector
    | Mul_Out_DVCons_DV of DVector * DVector
    | Div_Had_DM_DM of DNDArray * DNDArray
    | Div_Had_DM_DMCons of DNDArray * DNDArray
    | Div_Had_DMCons_DM of DNDArray * DNDArray
    | Pow_DM_DM of DNDArray * DNDArray
    | Pow_DM_DMCons of DNDArray * DNDArray
    | Pow_DMCons_DM of DNDArray * DNDArray
    | Atan2_DM_DM of DNDArray * DNDArray
    | Atan2_DM_DMCons of DNDArray * DNDArray
    | Atan2_DMCons_DM of DNDArray * DNDArray
    | Div_DM_D of DNDArray * DNumber
    | Div_DM_DCons of DNDArray * DNumber
    | Div_DMCons_D of DNDArray * DNumber
    | Div_D_DM of DNumber * DNDArray
    | Div_D_DMCons of DNumber * DNDArray
    | Div_DCons_DM of DNumber * DNDArray
    | Add_DM_D of DNDArray * DNumber
    | Add_DM_DCons of DNDArray
    | Add_DMCons_D of DNumber
    | Sub_DM_D of DNDArray * DNumber
    | Sub_DM_DCons of DNDArray
    | Sub_DMCons_D of DNumber
    | Sub_D_DM of DNumber * DNDArray
    | Sub_D_DMCons of DNumber
    | Sub_DCons_DM of DNDArray
    | Pow_DM_D of DNDArray * DNumber
    | Pow_DM_DCons of DNDArray * DNumber
    | Pow_DMCons_D of DNDArray * DNumber
    | Pow_D_DM of DNumber * DNDArray
    | Pow_D_DMCons of DNumber * DNDArray
    | Pow_DCons_DM of DNumber * DNDArray
    | Atan2_DM_D of DNDArray * DNumber
    | Atan2_DM_DCons of DNDArray * DNumber
    | Atan2_DMCons_D of DNDArray * DNumber
    | Atan2_D_DM of DNumber * DNDArray
    | Atan2_D_DMCons of DNumber * DNDArray
    | Atan2_DCons_DM of DNumber * DNDArray
    | Exp_DM of DNDArray
    | Log_DM of DNDArray
    | Log10_DM of DNDArray
    | Sin_DM of DNDArray
    | Cos_DM of DNDArray
    | Tan_DM of DNDArray
    | Neg_DM of DNDArray
    | Sqrt_DM of DNDArray
    | Sinh_DM of DNDArray
    | Cosh_DM of DNDArray
    | Tanh_DM of DNDArray
    | Asin_DM of DNDArray
    | Acos_DM of DNDArray
    | Atan_DM of DNDArray
    | Abs_DM of DNDArray
    | Sign_DM of DNDArray
    | Floor_DM of DNDArray
    | Ceil_DM of DNDArray
    | Round_DM of DNDArray
    | Transpose_DM of DNDArray
    | Make_DM_ofDs of DNumber []
    | Make_DMRows_ofDV of DVector
    | Make_DMRows_ofDVs of DVector []
    | AddItem_DM_D of DNDArray * int * int * DNumber
    | AddItem_DM_DCons of DNDArray
    | AddItem_DMCons_D of int * int * DNumber
    | Slice_DM of DNDArray * int * int
    | RowMatrix_DV of DVector
    | AddDiagonal_DM_DV of DNDArray * DVector
    | AddDiagonal_DM_DVCons of DNDArray
    | AddDiagonal_DMCons_DV of DVector
    | ReshapeCopy_DV_DM of DVector
    | Inverse_DM of DNDArray
    | Det_DM of DNDArray
    | ReLU_DM of DNDArray
    | Sigmoid_DM of DNDArray
    | Noop

/// Functional-oriented operations on vectors. Implementing functionality similar to FSharp.Collections.Array.
[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module DV = 
    // Note: map operations are not implemented on purpose. To benefit from the performance of BLAS ops, supplied element-wise operations are used. For example: "exp v" instead of "DV.map exp v"
    /// Creates a vector from array `a`
    let inline ofArray a = DVector.OfArray(a)
    
    /// Converts vector `v` into an array
    let inline toArray (v : DVector) = v.ToArray()
    
    /// Creates a copy of vector `v`
    let inline copy (v : DVector) = v.DeepCopy()
    
    /// Creates a vector with `n` elements, each with value `v`
    let inline create n (v : 'a) (backend : Backend<number>) = 
        let at = typeof<'a>
        if at.Equals(typeof<DNumber>) then DVector.OfArray(Array.create n (unbox<DNumber> (box v)))
        elif at.Equals(typeof<number>) then DV(backend.CreateDataBuffer(Array.create n (unbox<number> (box v))))
        elif at.Equals(typeof<int>) then 
            DV(backend.CreateDataBuffer(Array.create n (unbox<int> (box v) |> toNumber)))
        else fail_with_invalid_type_message()
    
    /// Creates a vector with `n` zero elements
    let inline zeroCreate n = DVector.ZeroN n
    
    /// Empty vector
    let empty = DVector.Zero
    
    /// Creates a vector of `n` elements, where each element is defined by function `f`
    let inline init n (f : int -> 'a) = 
        let at = typeof<'a>
        if at.Equals(typeof<DNumber>) then DVector.OfArray(Array.init n (unbox<int -> DNumber> (box f)))
        elif at.Equals(typeof<number>) then 
            DV(new NativeDataBuffer<number>(Array.init n (unbox<int -> number> (box f))))
        elif at.Equals(typeof<int>) then 
            DV(new NativeDataBuffer<number>((Array.init n (unbox<int -> int> (box f))) |> Array.map toNumber))
        else fail_with_invalid_type_message()
    
    /// Returns true if vector `v` is empty, otherwise returns false
    let isEmpty (v : DVector) = v.Length = 0
    
    /// Iterates function `f` over the elements of vector `v`
    let inline iter (f : DNumber -> unit) (v : DVector) = 
        v
        |> toArray
        |> Array.iter f
    
    /// Iterates function `f` over the elements of vector `v`. An element index is also supplied to `f`.
    let inline iteri (f : int -> DNumber -> unit) (v : DVector) = 
        v
        |> toArray
        |> Array.iteri f
    
    /// Iterates function `f` over the elements of vectors `v1` and `v2`
    let inline iter2 (f : DNumber -> DNumber -> unit) (v1 : DVector) (v2 : DVector) = 
        Array.iter2 f (v1 |> toArray) (v2 |> toArray)
    
    /// Iterates function `f` over the elements of vectors `v1` and `v2`. An element index is also supplied to `f`.
    let inline iteri2 (f : int -> DNumber -> DNumber -> unit) (v1 : DVector) (v2 : DVector) = 
        Array.iteri2 f (v1 |> toArray) (v2 |> toArray)
    
    /// Length of vector `v`
    let inline length (v : DVector) = v.Length
    
    /// L1 norm of vector `v`
    let inline l1norm (v : DVector) = DVector.L1Norm(v)
    
    /// L2 norm of vector `v`
    let inline l2norm (v : DVector) = DVector.L2Norm(v)
    
    /// Squared L2 norm of vector `v`
    let inline l2normSq (v : DVector) = DVector.L2NormSq(v)
    
    /// Maximum of the elements of vector `v`
    let inline max (v : DVector) = DVector.Max(v)
    
    /// Index of the maximum element of vector `v`
    let inline maxIndex (v : DVector) = DVector.MaxIndex(v)
    
    /// Minimum of the elements of vector `v`
    let inline min (v : DVector) = DVector.Min(v)
    
    /// Index of the minimum element of vector `v`
    let inline minIndex (v : DVector) = DVector.MinIndex(v)
    
    /// Mean of vector `v`
    let inline mean (v : DVector) = DVector.Mean(v)
    
    /// Average of vector `v`. Same with mean.
    let average = mean
    
    /// Standard deviation of vector `v`
    let inline standardDev (v : DVector) = DVector.StandardDev(v)
    
    /// Variance of vector `v`
    let inline variance (v : DVector) = DVector.Variance(v)
    
    /// Shift and scale the elements of vector `v` to have zero mean and unit variance
    let inline standardize (v : DVector) = DVector.Standardize(v)
    
    /// Shift and scale the elements of vector `v` to be in the range [0, 1]
    let inline normalize (v : DVector) = DVector.Normalize(v)
    
    /// L2 norm of vector `v`. Same with DV.l2norm.
    let inline norm (v : DVector) = DVector.L2Norm(v)
    
    /// Squared L2 norm of vector `v`. Same with DV.l2normSq.
    let inline normSq (v : DVector) = DVector.L2NormSq(v)
    
    // TODO: implement supNorm (infinity norm, with BLAS IDAMAX)
    /// Creates a vector where elements of `v1` are followed by elements of `v2`
    let inline append (v1 : DVector) (v2 : DVector) = DVector.Append(v1, v2)
    
    /// Creates a vector where elements of `v2` are followed by elements of `v1`
    let inline prepend (v1 : DVector) (v2 : DVector) = DVector.Append(v2, v1)
    
    /// Concatenates the given sequence of vectors `v` into one vector
    let inline concat (v : seq<DVector>) = Seq.fold append DVector.Zero v
    
    /// Splits vector `v` into a sequence of subvectors whose lengths are given in sequence `n`
    let inline split (n : seq<int>) (v : DVector) = DVector.Split(v, n)
    
    /// Splits vector `v` into `n` subvectors of equal length. The length of vector `v` must be an integer multiple of `n`.
    let inline splitEqual (n : int) (v : DVector) = DVector.Split(v, Array.create n (v.Length / n))
    
    /// Sums the elements of vector `v`
    let inline sum (v : DVector) = DVector.Sum(v)
    
    /// Creates a vector with `n` elements where the `i`-th element is one and the rest of the elements are zero
    let inline standardBasis (n : int) (i : int) = DV(NativeDataBuffer<number>(standardBasis n i))
    
    /// Creates a vector with `n` elements where the `i`-th element has value `v` and the rest of the elements are zero
    let inline standardBasisVal (n : int) (i : int) (v : number) = DV(NativeDataBuffer<number>(standardBasisVal n i v))
    
    /// Gets the unit vector codirectional with vector `v`
    let inline unitDV (v : DVector) = v / DVector.L2Norm(v)
    
    /// Converts matrix `m` into a vector by stacking its rows
    let inline ofDM (m : DNDArray) = DNDArray.ReshapeToDV(m)
    
    /// Creates a matrix with `m` rows from vector `v`
    let inline toDM (m : int) (v : DVector) = DVector.ReshapeToDM(m, v)
    
    // Experimental
    let inline toString (v : DVector) = v.ToString()
    let inline visualize (v : DVector) = v.Visualize()
    let inline visualizeAsDM (m : int) (v : DVector) = DVector.ReshapeToDM(m, v).Visualize()

/// Functional-oriented operations on matrices. Implementing functionality similar to FSharp.Collections.Array2D.
[<RequireQualifiedAccess>]
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module DM = 
    /// Creates a matrix with `m` rows from array `a`
    let inline ofArray m a (b : Backend<number>) = DNDArray.OfDNumberArray(m, a, b)
    
    /// Converts matrix `m` into an array by stacking its rows
    let inline toArray (m : DNDArray) = DNDArray.ReshapeToDV(m) |> DV.toArray
    
    /// Transpose of matrix `m`
    let inline transpose (m : DNDArray) = DNDArray.Transpose(m)
    
    /// Creates a matrix from a sequence of row vectors `s`
    let inline ofRows s = DNDArray.OfRows(s)
    
    /// Creates a matrix from a sequence of column vectors `s`
    let inline ofCols (s : seq<DVector>) = 
        s
        |> ofRows
        |> transpose
    
    /// Converts matrix `m` into a vector by stacking its rows
    let inline toDV (m : DNDArray) = DNDArray.ReshapeToDV(m)
    
    /// Creates a matrix with `m` rows from vector `v`
    let inline ofDV (m : int) (v : DVector) = DVector.ReshapeToDM(m, v)
    
    /// Number of columns in matrix `m`
    let inline cols (m : DNDArray) = m.Cols
    
    /// Number of rows in matrix `m`
    let inline rows (m : DNDArray) = m.Rows
    
    /// Creates a matrix with `m` rows and `n` columns, where all entries have value `v`
    let inline create m n (v : 'a) (b : Backend<float32>) = 
        let at = typeof<'a>
        if at.Equals(typeof<DNumber>) then DNDArray.OfDNumberArray(m, Array.create (m * n) (unbox<DNumber> (box v)), b)
        elif at.Equals(typeof<number>) then DNDArray.OfNumberArray(m, Array.create (m * n) (unbox<number> (box v)), b)
        elif at.Equals(typeof<int>) then DNDArray.OfNumberArray(m, Array.create (m * n) (unbox<number> (box v)), b)
        else fail_with_invalid_type_message()
    
    /// Creates a matrix with `m` rows and `n` columns, where all entries are zero
    let inline zeroCreate m n = DNDArray.ZeroMN m n
    
    /// Gets the diagonal of matrix `m`
    let inline diagonal (m : DNDArray) = DNDArray.Diagonal(m)
    
    /// Zero matrix
    let empty = DNDArray.Zero
    
    /// Returns true if matrix `m` is empty, otherwise returns false
    let isEmpty (m : DNDArray) = m.Length = 0
    
    /// Creates a matrix with `m` rows and `n` columns, where each element is given by function `f`
    let inline init m n (f : int -> int -> 'a) (b : Backend<number>) = 
        let at = typeof<'a>
        let frel i = f (i / m) (i % m)
        if at.Equals(typeof<DNumber>) then 
            let numbers = Seq.cast<DNumber> (Array.init (m * n) frel) |> Seq.toArray
            DNDArray.OfDNumberArray(m, numbers, b)
        elif at.Equals(typeof<number>) then 
            let numbers = Seq.cast<number> (Array.init (m * n) frel) |> Seq.toArray
            DNDArray.OfNumberArray(m, numbers, b)
        elif at.Equals(typeof<int>) then 
            let numbers = Seq.cast<number> (Array.init (m * n) frel) |> Seq.toArray
            DNDArray.OfNumberArray(m, numbers, b)
        else fail_with_invalid_type_message()
    
    /// Inverse of matrix `m`
    let inline inverse (m : DNDArray) = DNDArray.Inverse(m)
    
    /// Iterates function `f` over the entries of matrix `m`
    let inline iter (f : DNumber -> unit) (m : DNDArray) = 
        m
        |> toDV
        |> DV.iter f
    
    /// Iterates function `f` over the entries of matrices `m1` and `m2`
    let inline iter2 (f : DNumber -> DNumber -> unit) (m1 : DNDArray) (m2 : DNDArray) = 
        DV.iter2 f (m1 |> toDV) (m2 |> toDV)
    
    /// Total number of elements in matrix `m`
    let inline length (m : DNDArray) = m.Length
    
    /// Number of rows in matrix `m`. Same with DM.rows.
    let inline length1 (m : DNDArray) = m.Rows
    
    /// Number of columns in matrix `m`. Same with DM.cols.
    let inline length2 (m : DNDArray) = m.Cols
    
    /// Creates a copy of matrix `m`
    let inline copy (m : DNDArray) = m.DeepCopy()
    
    /// Determinant of matrix `m`
    let inline det (m : DNDArray) = DNDArray.Det(m)
    
    /// Maximum of the entries of matrix `m`
    let inline max (m : DNDArray) = DNDArray.Max(m)
    
    /// Index of the maximum entry of matrix `m`
    let inline maxIndex (m : DNDArray) = DNDArray.MaxIndex(m)
    
    /// Minimum of the entries of matrix `m`
    let inline min (m : DNDArray) = DNDArray.Min(m)
    
    /// Index of the minimum entry of matrix `m`
    let inline minIndex (m : DNDArray) = DNDArray.MinIndex(m)
    
    /// Mean of matrix `m`
    let inline mean (m : DNDArray) = DNDArray.Mean(m)
    
    /// Average of matrix `m`. Same with mean.
    let average = mean
    
    /// Standard deviation of matrix `m`
    let inline standardDev (m : DNDArray) = DNDArray.StandardDev(m)
    
    /// Variance of matrix `m`
    let inline variance (m : DNDArray) = DNDArray.Variance(m)
    
    /// Shift and scale the elements of matrix `m` to have zero mean and unit variance
    let inline standardize (m : DNDArray) = DNDArray.Standardize(m)
    
    /// Shift and scale the elements of matrix `m` to be in the range [0, 1]
    let inline normalize (m : DNDArray) = DNDArray.Normalize(m)
    
    /// Solve a system of linear equations Ax = b, where the coefficient matrix `m` has general form
    //    let inline solve (m:DNDArray) (v:DVector) = DNDArray.Solve(m, v)
    /// Solve a system of linear equations Ax = b, where the coefficient matrix `m` is symmetric
    //    let inline solveSymmetric (m:DNDArray) (v:DVector) = DNDArray.SolveSymmetric(m, v)
    /// Sums the elements of matrix `m`
    let inline sum (m : DNDArray) = DNDArray.Sum(m)
    
    /// Trace of matrix `m`
    let inline trace (m : DNDArray) = DNDArray.Trace(m)
    
    /// Experimental
    let inline toString (m : DNDArray) = m.ToString()
    
    let inline visualize (m : DNDArray) = m.Visualize()
    let inline visualizeAsDV (m : DNDArray) = DNDArray.ReshapeToDV(m).Visualize()

/// D, DV, DM operations (automatically opened)
[<AutoOpen>]
module DOps = 
    /// Explicit conversion between types where it is permitted. For example: DV -> number[], number[,] -> DM
    let inline convert (v : ^a) : ^b = ((^a or ^b) : (static member op_Explicit : ^a -> ^b) v)
    
    /// Create a vector from sequence `v`
    let inline toDV (v : seq<_>) = 
        match v with
        | :? seq<DNumber> as v -> 
            v
            |> Seq.toArray
            |> DV.ofArray
        | _ -> 
            DV(NativeDataBuffer<number>(v
                                        |> Seq.toArray
                                        |> Array.map toNumber))
    
    /// Make forward AD type, with tag `i`, primal `p` and tangent `t`
    let inline makeForward i (t : ^a) (p : ^a) = (^a : (member GetForward : ^a -> uint32 -> ^a) p, t, i)
    
    /// Make reverse AD type, with tag `i` and primal `p`
    let inline makeReverse i (p : ^a) = (^a : (member GetReverse : uint32 -> ^a) p, i)
    
    /// Get the primal value of `d`
    let inline primal (d : ^a when ^a : (member P : ^a)) = (^a : (member P : ^a) d)
    /// Get the deepest primal value of `d`
    let inline primalDeep (d : ^a when ^a : (member PD : ^a)) = (^a : (member PD : ^a) d)
    /// Get the tangent value of `d`
    let inline tangent (d : ^a when ^a : (member T : ^a)) = (^a : (member T : ^a) d)
    /// Get the adjoint value of `d`
    let inline adjoint (d : ^a when ^a : (member A : ^a)) = (^a : (member A : ^a) d)
    
    /// Get the primal and tangent values of `d`, as a tuple
    let inline primalTangent d = d |> primal, d |> tangent
    
    /// Resets the adjoints of all the values in the evaluation trace of `d`, preparing for a new reverse propagation
    let reverseReset (d : obj) = 
        let rec resetRec (ds : obj list) = 
            match ds with
            | [] -> ()
            | d :: t -> 
                match d with
                | :? DNumber as d -> 
                    match d with
                    | DR(_, _, o, _, _) -> 
                        d.A <- D number0
                        d.F <- d.F + 1u
                        if d.F = 1u then 
                            match o with
                            | Add_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Add_D_DCons(a) -> resetRec (box a :: t)
                            | Sub_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_D_DCons(a) -> resetRec (box a :: t)
                            | Sub_DCons_D(b) -> resetRec (box b :: t)
                            | Mul_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_D_DCons(a, _) -> resetRec (box a :: t)
                            | Div_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Div_D_DCons(a, _) -> resetRec (box a :: t)
                            | Div_DCons_D(_, b) -> resetRec (box b :: t)
                            | Pow_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_D_DCons(a, _) -> resetRec (box a :: t)
                            | Pow_DCons_D(_, b) -> resetRec (box b :: t)
                            | Atan2_D_D(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_D_DCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DCons_D(_, b) -> resetRec (box b :: t)
                            | Log_D(a) -> resetRec (box a :: t)
                            | Log10_D(a) -> resetRec (box a :: t)
                            | Exp_D(a) -> resetRec (box a :: t)
                            | Sin_D(a) -> resetRec (box a :: t)
                            | Cos_D(a) -> resetRec (box a :: t)
                            | Tan_D(a) -> resetRec (box a :: t)
                            | Neg_D(a) -> resetRec (box a :: t)
                            | Sqrt_D(a) -> resetRec (box a :: t)
                            | Sinh_D(a) -> resetRec (box a :: t)
                            | Cosh_D(a) -> resetRec (box a :: t)
                            | Tanh_D(a) -> resetRec (box a :: t)
                            | Asin_D(a) -> resetRec (box a :: t)
                            | Acos_D(a) -> resetRec (box a :: t)
                            | Atan_D(a) -> resetRec (box a :: t)
                            | Abs_D(a) -> resetRec (box a :: t)
                            | Sign_D(a) -> resetRec (box a :: t)
                            | Floor_D(a) -> resetRec (box a :: t)
                            | Ceil_D(a) -> resetRec (box a :: t)
                            | Round_D(a) -> resetRec (box a :: t)
                            | Mul_Dot_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_Dot_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Sum_DV(a) -> resetRec (box a :: t)
                            | L1Norm_DV(a) -> resetRec (box a :: t)
                            | L2NormSq_DV(a) -> resetRec (box a :: t)
                            | L2Norm_DV(a) -> resetRec (box a :: t)
                            | Item_DV(a, _) -> resetRec (box a :: t)
                            | Sum_DM(a) -> resetRec (box a :: t)
                            | Item_DM(a, _, _) -> resetRec (box a :: t)
                            | Det_DM(a) -> resetRec (box a :: t)
                            | ReLU_D(a) -> resetRec (box a :: t)
                            | Sigmoid_D(a) -> resetRec (box a :: t)
                            | LogSumExp_DV(a) -> resetRec (box a :: t)
                            | FixedPoint_D(b, _, _, _) -> resetRec (box b :: t)
                            | _ -> resetRec t
                        else resetRec t
                    | _ -> resetRec t
                | :? DVector as d -> 
                    match d with
                    | DVR(_, _, o, _, _) -> 
                        d.A <- DVector.ZeroN d.Length
                        d.F <- d.F + 1u
                        if d.F = 1u then 
                            match o with
                            | Add_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Add_DV_DVCons(a) -> resetRec (box a :: t)
                            | Add_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Add_DV_DCons(a) -> resetRec (box a :: t)
                            | Add_DVCons_D(b) -> resetRec (box b :: t)
                            | Sub_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_DV_DVCons(a) -> resetRec (box a :: t)
                            | Sub_DVCons_DV(a) -> resetRec (box a :: t)
                            | Sub_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_DV_DCons(a) -> resetRec (box a :: t)
                            | Sub_DVCons_D(b) -> resetRec (box b :: t)
                            | Sub_D_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_D_DVCons(a) -> resetRec (box a :: t)
                            | Sub_DCons_DV(b) -> resetRec (box b :: t)
                            | Mul_Had_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_Had_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Mul_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_DV_DCons(a, _) -> resetRec (box a :: t)
                            | Mul_DVCons_D(_, b) -> resetRec (box b :: t)
                            | Mul_DM_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_DM_DVCons(a, _) -> resetRec (box a :: t)
                            | Mul_DMCons_DV(_, b) -> resetRec (box b :: t)
                            | Mul_DV_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_DV_DMCons(a, _) -> resetRec (box a :: t)
                            | Mul_DVCons_DM(_, b) -> resetRec (box b :: t)
                            | Div_Had_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Div_Had_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Div_Had_DVCons_DV(_, b) -> resetRec (box b :: t)
                            | Div_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Div_DV_DCons(a, _) -> resetRec (box a :: t)
                            | Div_DVCons_D(_, b) -> resetRec (box b :: t)
                            | Div_D_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Div_D_DVCons(a, _) -> resetRec (box a :: t)
                            | Div_DCons_DV(_, b) -> resetRec (box b :: t)
                            | Pow_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Pow_DVCons_DV(_, b) -> resetRec (box b :: t)
                            | Atan2_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DVCons_DV(_, b) -> resetRec (box b :: t)
                            | Pow_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_DV_DCons(a, _) -> resetRec (box a :: t)
                            | Pow_DVCons_D(_, b) -> resetRec (box b :: t)
                            | Pow_D_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_D_DVCons(a, _) -> resetRec (box a :: t)
                            | Pow_DCons_DV(_, b) -> resetRec (box b :: t)
                            | Atan2_DV_D(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_DV_DCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DVCons_D(_, b) -> resetRec (box b :: t)
                            | Atan2_D_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_D_DVCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DCons_DV(_, b) -> resetRec (box b :: t)
                            | Log_DV(a) -> resetRec (box a :: t)
                            | Log10_DV(a) -> resetRec (box a :: t)
                            | Exp_DV(a) -> resetRec (box a :: t)
                            | Sin_DV(a) -> resetRec (box a :: t)
                            | Cos_DV(a) -> resetRec (box a :: t)
                            | Tan_DV(a) -> resetRec (box a :: t)
                            | Neg_DV(a) -> resetRec (box a :: t)
                            | Sqrt_DV(a) -> resetRec (box a :: t)
                            | Sinh_DV(a) -> resetRec (box a :: t)
                            | Cosh_DV(a) -> resetRec (box a :: t)
                            | Tanh_DV(a) -> resetRec (box a :: t)
                            | Asin_DV(a) -> resetRec (box a :: t)
                            | Acos_DV(a) -> resetRec (box a :: t)
                            | Atan_DV(a) -> resetRec (box a :: t)
                            | Abs_DV(a) -> resetRec (box a :: t)
                            | Sign_DV(a) -> resetRec (box a :: t)
                            | Floor_DV(a) -> resetRec (box a :: t)
                            | Ceil_DV(a) -> resetRec (box a :: t)
                            | Round_DV(a) -> resetRec (box a :: t)
                            | Make_DV_ofDs(a) -> 
                                resetRec (List.append (a
                                                       |> Array.map box
                                                       |> List.ofArray) t)
                            | SliceRow_DM(a, _, _) -> resetRec (box a :: t)
                            | SliceCol_DM(a, _, _) -> resetRec (box a :: t)
                            | Solve_DM_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Solve_DM_DVCons(a, _) -> resetRec (box a :: t)
                            | Solve_DMCons_DV(_, b) -> resetRec (box b :: t)
                            | Append_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Append_DV_DVCons(a) -> resetRec (box a :: t)
                            | Append_DVCons_DV(b) -> resetRec (box b :: t)
                            | Split_DV(a, _) -> resetRec (box a :: t)
                            | AddItem_DV_D(a, _, b) -> resetRec (box a :: box b :: t)
                            | AddItem_DV_DCons(a) -> resetRec (box a :: t)
                            | AddItem_DVCons_D(_, b) -> resetRec (box b :: t)
                            | AddSubVector_DV_DV(a, _, b) -> resetRec (box a :: box b :: t)
                            | AddSubVector_DV_DVCons(a) -> resetRec (box a :: t)
                            | AddSubVector_DVCons_DV(_, b) -> resetRec (box b :: t)
                            | ReshapeCopy_DM_DV(a) -> resetRec (box a :: t)
                            | Slice_DV(a, _) -> resetRec (box a :: t)
                            | Diagonal_DM(a) -> resetRec (box a :: t)
                            | ReLU_DV(a) -> resetRec (box a :: t)
                            | Sigmoid_DV(a) -> resetRec (box a :: t)
                            | _ -> resetRec t
                        else resetRec t
                    | _ -> resetRec t
                | :? DNDArray as d -> 
                    match d with
                    | DMR(_, _, o, _, _) -> 
                        d.A <- DNDArray.ZeroMN d.Rows d.Cols (Backend(d))
                        d.F <- d.F + 1u
                        if d.F = 1u then 
                            match o with
                            | Add_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Add_DM_DMCons(a) -> resetRec (box a :: t)
                            | Sub_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_DM_DMCons(a) -> resetRec (box a :: t)
                            | Sub_DMCons_DM(a) -> resetRec (box a :: t)
                            | Mul_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_DM_DMCons(a, _) -> resetRec (box a :: t)
                            | Mul_Had_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_Had_DM_DMCons(a, _) -> resetRec (box a :: t)
                            | Mul_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_DM_DCons(a, _) -> resetRec (box a :: t)
                            | Mul_DMCons_D(_, b) -> resetRec (box b :: t)
                            | Mul_Out_DV_DV(a, b) -> resetRec (box a :: box b :: t)
                            | Mul_Out_DV_DVCons(a, _) -> resetRec (box a :: t)
                            | Mul_Out_DVCons_DV(_, b) -> resetRec (box b :: t)
                            | Div_Had_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Div_Had_DM_DMCons(a, _) -> resetRec (box a :: t)
                            | Div_Had_DMCons_DM(_, b) -> resetRec (box b :: t)
                            | Pow_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_DM_DMCons(a, _) -> resetRec (box a :: t)
                            | Pow_DMCons_DM(_, b) -> resetRec (box b :: t)
                            | Atan2_DM_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_DM_DMCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DMCons_DM(_, b) -> resetRec (box b :: t)
                            | Div_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Div_DM_DCons(a, _) -> resetRec (box a :: t)
                            | Div_DMCons_D(_, b) -> resetRec (box b :: t)
                            | Div_D_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Div_D_DMCons(a, _) -> resetRec (box a :: t)
                            | Div_DCons_DM(_, b) -> resetRec (box b :: t)
                            | Add_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Add_DM_DCons(a) -> resetRec (box a :: t)
                            | Add_DMCons_D(b) -> resetRec (box b :: t)
                            | Sub_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_DM_DCons(a) -> resetRec (box a :: t)
                            | Sub_DMCons_D(b) -> resetRec (box b :: t)
                            | Sub_D_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Sub_D_DMCons(a) -> resetRec (box a :: t)
                            | Sub_DCons_DM(b) -> resetRec (box b :: t)
                            | Pow_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_DM_DCons(a, _) -> resetRec (box a :: t)
                            | Pow_DMCons_D(_, b) -> resetRec (box b :: t)
                            | Pow_D_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Pow_D_DMCons(a, _) -> resetRec (box a :: t)
                            | Pow_DCons_DM(_, b) -> resetRec (box b :: t)
                            | Atan2_DM_D(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_DM_DCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DMCons_D(_, b) -> resetRec (box b :: t)
                            | Atan2_D_DM(a, b) -> resetRec (box a :: box b :: t)
                            | Atan2_D_DMCons(a, _) -> resetRec (box a :: t)
                            | Atan2_DCons_DM(_, b) -> resetRec (box b :: t)
                            | Log_DM(a) -> resetRec (box a :: t)
                            | Log10_DM(a) -> resetRec (box a :: t)
                            | Exp_DM(a) -> resetRec (box a :: t)
                            | Sin_DM(a) -> resetRec (box a :: t)
                            | Cos_DM(a) -> resetRec (box a :: t)
                            | Tan_DM(a) -> resetRec (box a :: t)
                            | Neg_DM(a) -> resetRec (box a :: t)
                            | Sqrt_DM(a) -> resetRec (box a :: t)
                            | Sinh_DM(a) -> resetRec (box a :: t)
                            | Cosh_DM(a) -> resetRec (box a :: t)
                            | Tanh_DM(a) -> resetRec (box a :: t)
                            | Asin_DM(a) -> resetRec (box a :: t)
                            | Acos_DM(a) -> resetRec (box a :: t)
                            | Atan_DM(a) -> resetRec (box a :: t)
                            | Abs_DM(a) -> resetRec (box a :: t)
                            | Sign_DM(a) -> resetRec (box a :: t)
                            | Floor_DM(a) -> resetRec (box a :: t)
                            | Ceil_DM(a) -> resetRec (box a :: t)
                            | Round_DM(a) -> resetRec (box a :: t)
                            | Transpose_DM(a) -> resetRec (box a :: t)
                            | Make_DM_ofDs(a) -> 
                                resetRec (List.append (a
                                                       |> Array.map box
                                                       |> List.ofArray) t)
                            | AddItem_DM_D(a, _, _, b) -> resetRec (box a :: box b :: t)
                            | AddItem_DM_DCons(a) -> resetRec (box a :: t)
                            | AddItem_DMCons_D(_, _, b) -> resetRec (box b :: t)
                            | Slice_DM(a, _, _) -> resetRec (box a :: t)
                            | AddDiagonal_DM_DV(a, b) -> resetRec (box a :: box b :: t)
                            | AddDiagonal_DM_DVCons(a) -> resetRec (box a :: t)
                            | AddDiagonal_DMCons_DV(b) -> resetRec (box b :: t)
                            | ReshapeCopy_DV_DM(a) -> resetRec (box a :: t)
                            | Inverse_DM(a) -> resetRec (box a :: t)
                            | ReLU_DM(a) -> resetRec (box a :: t)
                            | Sigmoid_DM(a) -> resetRec (box a :: t)
                            | _ -> resetRec t
                        else resetRec t
                    | _ -> resetRec t
                | _ -> resetRec t
        resetRec [ d ]
    
    /// Pushes the adjoint `v` backward through the evaluation trace of `d`
    let reversePush (v : obj) (d : obj) = 
        let inline bx v d = box v, box d
        
        let rec pushRec (ds : (obj * obj) list) = 
            match ds with
            | [] -> ()
            | (v, d) :: t -> 
                match d with
                | :? DNumber as d -> 
                    match d with
                    | DR(_, _, o, _, _) -> 
                        d.A <- d.A + (v :?> DNumber)
                        d.F <- d.F - 1u
                        if d.F = 0u then 
                            match o with
                            | Add_D_D(a, b) -> pushRec ((bx d.A a) :: (bx d.A b) :: t)
                            | Add_D_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_D_D(a, b) -> pushRec ((bx d.A a) :: (bx -d.A b) :: t)
                            | Sub_D_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DCons_D(b) -> pushRec ((bx -d.A b) :: t)
                            | Mul_D_D(a, b) -> pushRec ((bx (d.A * b.P) a) :: (bx (d.A * a.P) b) :: t)
                            | Mul_D_DCons(a, cons) -> pushRec ((bx (d.A * cons) a) :: t)
                            | Div_D_D(a, b) -> pushRec ((bx (d.A / b.P) a) :: (bx (d.A * (-a.P / (b.P * b.P))) b) :: t)
                            | Div_D_DCons(a, cons) -> pushRec ((bx (d.A / cons) a) :: t)
                            | Div_DCons_D(cons, b) -> pushRec ((bx (d.A * (-cons / (b.P * b.P))) b) :: t)
                            | Pow_D_D(a, b) -> 
                                pushRec 
                                    ((bx (d.A * (a.P ** (b.P - D number1)) * b.P) a) 
                                     :: (bx (d.A * (a.P ** b.P) * log a.P) b) :: t)
                            | Pow_D_DCons(a, cons) -> pushRec ((bx (d.A * (a.P ** (cons - D number1)) * cons) a) :: t)
                            | Pow_DCons_D(cons, b) -> pushRec ((bx (d.A * (cons ** b.P) * log cons) b) :: t)
                            | Atan2_D_D(a, b) -> 
                                let denom = a.P * a.P + b.P * b.P
                                pushRec ((bx (d.A * b.P / denom) a) :: (bx (d.A * (-a.P) / denom) b) :: t)
                            | Atan2_D_DCons(a, cons) -> pushRec ((bx (d.A * cons / (a.P * a.P + cons * cons)) a) :: t)
                            | Atan2_DCons_D(cons, b) -> 
                                pushRec ((bx (d.A * (-cons) / (cons * cons + b.P * b.P)) b) :: t)
                            | Log_D(a) -> pushRec ((bx (d.A / a.P) a) :: t)
                            | Log10_D(a) -> pushRec ((bx (d.A / (a.P * log10Val())) a) :: t)
                            | Exp_D(a) -> pushRec ((bx (d.A * d.P) a) :: t) // d.P = exp a.P
                            | Sin_D(a) -> pushRec ((bx (d.A * cos a.P) a) :: t)
                            | Cos_D(a) -> pushRec ((bx (d.A * (-sin a.P)) a) :: t)
                            | Tan_D(a) -> 
                                let seca = D number1 / cos a.P
                                pushRec ((bx (d.A * seca * seca) a) :: t)
                            | Neg_D(a) -> pushRec ((bx -d.A a) :: t)
                            | Sqrt_D(a) -> pushRec ((bx (d.A / (D number2 * d.P)) a) :: t) // d.P = sqrt a.P
                            | Sinh_D(a) -> pushRec ((bx (d.A * cosh a.P) a) :: t)
                            | Cosh_D(a) -> pushRec ((bx (d.A * sinh a.P) a) :: t)
                            | Tanh_D(a) -> 
                                let secha = D number1 / cosh a.P
                                pushRec ((bx (d.A * secha * secha) a) :: t)
                            | Asin_D(a) -> pushRec ((bx (d.A / sqrt (D number1 - a.P * a.P)) a) :: t)
                            | Acos_D(a) -> pushRec ((bx (-d.A / sqrt (D number1 - a.P * a.P)) a) :: t)
                            | Atan_D(a) -> pushRec ((bx (d.A / (D number1 + a.P * a.P)) a) :: t)
                            | Abs_D(a) -> pushRec ((bx (d.A * DNumber.Sign(a.P)) a) :: t)
                            | Sign_D(a) -> pushRec ((bx DNumber.Zero a) :: t)
                            | Floor_D(a) -> pushRec ((bx DNumber.Zero a) :: t)
                            | Ceil_D(a) -> pushRec ((bx DNumber.Zero a) :: t)
                            | Round_D(a) -> pushRec ((bx DNumber.Zero a) :: t)
                            | Mul_Dot_DV_DV(a, b) -> pushRec ((bx (d.A * b.P) a) :: (bx (d.A * a.P) b) :: t)
                            | Mul_Dot_DV_DVCons(a, cons) -> pushRec ((bx (d.A * cons) a) :: t)
                            | Sum_DV(a) -> pushRec ((bx (DV.create a.Length d.A) a) :: t)
                            | L1Norm_DV(a) -> pushRec ((bx (d.A * DVector.Sign a.P) a) :: t)
                            | L2NormSq_DV(a) -> pushRec ((bx (d.A * (D number2) * a.P) a) :: t)
                            | L2Norm_DV(a) -> pushRec ((bx ((d.A / d.P) * a.P) a) :: t)
                            | Item_DV(a, i) -> 
                                a.A <- DVector.AddItem(a.A, i, d.A)
                                pushRec ((bx DVector.Zero a) :: t)
                            | Sum_DM(a) -> pushRec ((bx (DM.create a.Rows a.Cols d.A (Backend(a))) a) :: t)
                            | Item_DM(a, i, j) -> 
                                a.A <- DNDArray.AddItem(a.A, i, j, d.A)
                                pushRec ((bx DNDArray.Zero a) :: t)
                            | Det_DM(a) -> pushRec ((bx (d.T * d.P * DNDArray.Transpose(DNDArray.Inverse(a))) a) :: t) // Check this
                            | ReLU_D(a) -> pushRec ((bx (d.A * ((DNumber.Sign(a.P) + number1) / number2)) a) :: t)
                            | Sigmoid_D(a) -> pushRec ((bx (d.A * d.P * (number1 - d.P)) a) :: t) // d.P = D.Sigmoid(a.P)
                            | LogSumExp_DV(a) -> pushRec ((bx ((d.A / exp d.P) * exp a.P) a) :: t) // d.P = DV.LogSumExp(a.P)
                            | FixedPoint_D(b, bfirst, aprev, alast) -> 
                                // Christianson (1994)
                                let imax = DiffSharp.Config.GlobalConfig.FixedPointMaxIterations
                                let eps = D(FixedPointEpsilon())
                                let mutable i = 0
                                let r = d.A
                                reverseReset alast
                                pushRec [ (box r, box alast) ]
                                while i < imax do
                                    i <- i + 1
                                    if i >= imax then 
                                        //printfn "Fixed point reverse iteration timeout, i = %i" i
                                        ignore()
                                    else if abs (aprev.A + r - alast.A) <= eps then 
                                        //printfn "Fixed point reverse iteration converged, i = %i" i
                                        i <- imax
                                    else 
                                        reverseReset alast
                                        pushRec [ (box (r + aprev.A), box alast) ]
                                pushRec ((bx (bfirst.A) b) :: t) // Propogate converged adjoint back towards the original b at the beginning of the fixed point iteration
                            | _ -> pushRec t
                        else pushRec t
                    | _ -> pushRec t
                | :? DVector as d -> 
                    match d with
                    | DVR(_, _, o, _, _) -> 
                        d.A <- d.A + (v :?> DVector)
                        d.F <- d.F - 1u
                        if d.F = 0u then 
                            match o with
                            | Add_DV_DV(a, b) -> pushRec ((bx d.A a) :: (bx d.A b) :: t)
                            | Add_DV_DVCons(a) -> pushRec ((bx d.A a) :: t)
                            | Add_DV_D(a, b) -> pushRec ((bx d.A a) :: (bx (DVector.Sum(d.A)) b) :: t)
                            | Add_DV_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Add_DVCons_D(b) -> pushRec ((bx (DVector.Sum(d.A)) b) :: t)
                            | Sub_DV_DV(a, b) -> pushRec ((bx d.A a) :: (bx -d.A b) :: t)
                            | Sub_DV_DVCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DVCons_DV(a) -> pushRec ((bx -d.A a) :: t)
                            | Sub_DV_D(a, b) -> pushRec ((bx d.A a) :: (bx -(DVector.Sum(d.A)) b) :: t)
                            | Sub_DV_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DVCons_D(b) -> pushRec ((bx -(DVector.Sum(d.A)) b) :: t)
                            | Sub_D_DV(a, b) -> pushRec ((bx (DVector.Sum(d.A)) a) :: (bx -d.A b) :: t)
                            | Sub_D_DVCons(a) -> pushRec ((bx (DVector.Sum(d.A)) a) :: t)
                            | Sub_DCons_DV(b) -> pushRec ((bx -d.A b) :: t)
                            | Mul_Had_DV_DV(a, b) -> pushRec ((bx (d.A .* b.P) a) :: (bx (d.A .* a.P) b) :: t)
                            | Mul_Had_DV_DVCons(a, cons) -> pushRec ((bx (d.A .* cons) a) :: t)
                            | Mul_DV_D(a, b) -> pushRec ((bx (d.A * b.P) a) :: (bx (d.A * a.P) b) :: t)
                            | Mul_DV_DCons(a, cons) -> pushRec ((bx (d.A * cons) a) :: t)
                            | Mul_DVCons_D(cons, b) -> pushRec ((bx (d.A * cons) b) :: t)
                            | Mul_DM_DV(a, b) -> 
                                pushRec ((bx (d.A &* b.P) a) :: (bx (DNDArray.Transpose(a.P) * d.A) b) :: t)
                            | Mul_DM_DVCons(a, cons) -> pushRec ((bx (d.A &* cons) a) :: t)
                            | Mul_DMCons_DV(cons, b) -> pushRec ((bx (DNDArray.Transpose(cons) * d.A) b) :: t)
                            | Mul_DV_DM(a, b) -> 
                                pushRec ((bx (d.A * DNDArray.Transpose(b.P)) a) :: (bx (a.P &* d.A) b) :: t)
                            | Mul_DV_DMCons(a, cons) -> pushRec ((bx (d.A * DNDArray.Transpose(cons)) a) :: t)
                            | Mul_DVCons_DM(cons, b) -> pushRec ((bx (cons &* d.A) b) :: t)
                            | Div_Had_DV_DV(a, b) -> 
                                pushRec ((bx (d.A ./ b.P) a) :: (bx (d.A .* (-a.P ./ (b.P .* b.P))) b) :: t)
                            | Div_Had_DV_DVCons(a, cons) -> pushRec ((bx (d.A ./ cons) a) :: t)
                            | Div_Had_DVCons_DV(cons, b) -> pushRec ((bx (d.A .* (-cons ./ (b.P .* b.P))) b) :: t)
                            | Div_DV_D(a, b) -> pushRec ((bx (d.A / b.P) a) :: (bx (d.A * (-a.P / (b.P * b.P))) b) :: t)
                            | Div_DV_DCons(a, cons) -> pushRec ((bx (d.A / cons) a) :: t)
                            | Div_DVCons_D(cons, b) -> pushRec ((bx (d.A * (-cons / (b.P * b.P))) b) :: t)
                            | Div_D_DV(a, b) -> 
                                pushRec ((bx (DVector.Sum(d.A ./ b.P)) a) :: (bx (d.A .* (-a.P / (b.P .* b.P))) b) :: t)
                            | Div_D_DVCons(a, cons) -> pushRec ((bx (DVector.Sum(d.A ./ cons)) a) :: t)
                            | Div_DCons_DV(cons, b) -> pushRec ((bx (d.A .* (-cons / (b.P .* b.P))) b) :: t)
                            | Pow_DV_DV(a, b) -> 
                                pushRec 
                                    ((bx (d.A .* (a.P ** (b.P - D number1)) .* b.P) a) 
                                     :: (bx (d.A .* (a.P ** b.P) .* log a.P) b) :: t)
                            | Pow_DV_DVCons(a, cons) -> 
                                pushRec ((bx (d.A .* (a.P ** (cons - D number1)) .* cons) a) :: t)
                            | Pow_DVCons_DV(cons, b) -> pushRec ((bx (d.A .* (cons ** b.P) .* log cons) b) :: t)
                            | Atan2_DV_DV(a, b) -> 
                                let denom = (a.P .* a.P) + (b.P .* b.P)
                                pushRec ((bx (d.A .* b.P ./ denom) a) :: (bx (d.A .* (-a.P) ./ denom) b) :: t)
                            | Atan2_DV_DVCons(a, cons) -> 
                                pushRec ((bx (d.A .* cons ./ ((a.P .* a.P) + (cons .* cons))) a) :: t)
                            | Atan2_DVCons_DV(cons, b) -> 
                                pushRec ((bx (d.A .* (-cons) ./ ((cons .* cons) + (b.P .* b.P))) b) :: t)
                            | Pow_DV_D(a, b) -> 
                                pushRec 
                                    ((bx (d.A .* (a.P ** (b.P - D number1)) * b.P) a) 
                                     :: (bx (DVector.Sum(d.A .* (a.P ** b.P) .* log a.P)) b) :: t)
                            | Pow_DV_DCons(a, cons) -> pushRec ((bx (d.A .* (a.P ** (cons - D number1)) * cons) a) :: t)
                            | Pow_DVCons_D(cons, b) -> 
                                pushRec ((bx (DVector.Sum(d.A .* (cons ** b.P) .* log cons)) b) :: t)
                            | Pow_D_DV(a, b) -> 
                                pushRec 
                                    ((bx (DVector.Sum(d.A .* (DVector.Pow(a.P, b.P - D number1)) .* b.P)) a) 
                                     :: (bx (d.A .* (DVector.Pow(a.P, b.P)) * log a.P) b) :: t)
                            | Pow_D_DVCons(a, cons) -> 
                                pushRec ((bx (DVector.Sum(d.A .* (DVector.Pow(a.P, cons - D number1)) .* cons)) a) :: t)
                            | Pow_DCons_DV(cons, b) -> 
                                pushRec ((bx (d.A .* (DVector.Pow(cons, b.P)) * log cons) b) :: t)
                            | Atan2_DV_D(a, b) -> 
                                let denom = (a.P .* a.P) + (b.P * b.P)
                                pushRec 
                                    ((bx (d.A * b.P ./ denom) a) :: (bx (DVector.Sum(d.A .* (-a.P) ./ denom)) b) :: t)
                            | Atan2_DV_DCons(a, cons) -> 
                                pushRec ((bx (d.A * cons ./ ((a.P .* a.P) + (cons * cons))) a) :: t)
                            | Atan2_DVCons_D(cons, b) -> 
                                pushRec ((bx (DVector.Sum(d.A .* (-cons) ./ ((cons .* cons) + (b.P * b.P)))) b) :: t)
                            | Atan2_D_DV(a, b) -> 
                                let denom = (a.P * a.P) + (b.P .* b.P)
                                pushRec 
                                    ((bx (DVector.Sum(d.A .* b.P ./ denom)) a) :: (bx (d.A * (-a.P) ./ denom) b) :: t)
                            | Atan2_D_DVCons(a, cons) -> 
                                pushRec ((bx (DVector.Sum(d.A .* cons ./ ((a.P * a.P) + (cons .* cons)))) a) :: t)
                            | Atan2_DCons_DV(cons, b) -> 
                                pushRec ((bx (d.A * (-cons) ./ ((cons * cons) + (b.P .* b.P))) b) :: t)
                            | Log_DV(a) -> pushRec ((bx (d.A ./ a.P) a) :: t)
                            | Log10_DV(a) -> pushRec ((bx (d.A ./ (a.P * log10Val())) a) :: t)
                            | Exp_DV(a) -> pushRec ((bx (d.A .* d.P) a) :: t) // d.P = exp a.P
                            | Sin_DV(a) -> pushRec ((bx (d.A .* cos a.P) a) :: t)
                            | Cos_DV(a) -> pushRec ((bx (-d.A .* sin a.P) a) :: t)
                            | Tan_DV(a) -> 
                                let seca = D number1 / cos a.P
                                pushRec ((bx (d.A .* seca .* seca) a) :: t)
                            | Neg_DV(a) -> pushRec ((bx -d.A a) :: t)
                            | Sqrt_DV(a) -> pushRec ((bx (d.A ./ (number2 * d.P)) a) :: t) // d.P = sqrt a.P
                            | Sinh_DV(a) -> pushRec ((bx (d.A .* cosh a.P) a) :: t)
                            | Cosh_DV(a) -> pushRec ((bx (d.A .* sinh a.P) a) :: t)
                            | Tanh_DV(a) -> 
                                let secha = D number1 / cosh a.P
                                pushRec ((bx (d.A .* secha .* secha) a) :: t)
                            | Asin_DV(a) -> pushRec ((bx (d.A ./ sqrt (D number1 - (a.P .* a.P))) a) :: t)
                            | Acos_DV(a) -> pushRec ((bx (-d.A ./ sqrt (D number1 - (a.P .* a.P))) a) :: t)
                            | Atan_DV(a) -> pushRec ((bx (d.A ./ (D number1 + (a.P .* a.P))) a) :: t)
                            | Abs_DV(a) -> pushRec ((bx (d.A .* DVector.Sign a.P) a) :: t)
                            | Sign_DV(a) -> pushRec ((bx DVector.Zero a) :: t)
                            | Floor_DV(a) -> pushRec ((bx DVector.Zero a) :: t)
                            | Ceil_DV(a) -> pushRec ((bx DVector.Zero a) :: t)
                            | Round_DV(a) -> pushRec ((bx DVector.Zero a) :: t)
                            | Make_DV_ofDs(a) -> 
                                pushRec (t |> List.append (a
                                                           |> Array.mapi (fun i v -> (bx d.A.[i] v))
                                                           |> List.ofArray))
                            | Solve_DM_DV(a, b) -> 
                                let ba = DNDArray.Solve(DNDArray.Transpose(a), d.A)
                                pushRec ((bx (-ba &* d.A) a) :: (bx (ba) b) :: t)
                            | Solve_DM_DVCons(a, cons) -> 
                                let ba = DNDArray.Solve(DNDArray.Transpose(a), d.A)
                                pushRec ((bx (-ba &* d.A) a) :: t)
                            | Solve_DMCons_DV(cons, b) -> 
                                let ba = DNDArray.Solve(DNDArray.Transpose(cons), d.A)
                                pushRec ((bx ba b) :: t)
                            | Append_DV_DV(a, b) -> 
                                a.A <- a.A + d.A.[..(a.Length - 1)]
                                b.A <- b.A + d.A.[a.Length..]
                                pushRec ((bx DVector.Zero a) :: (bx DVector.Zero b) :: t)
                            | Append_DV_DVCons(a) -> 
                                a.A <- a.A + d.A.[..(a.Length - 1)]
                                pushRec ((bx DVector.Zero a) :: t)
                            | Append_DVCons_DV(b) -> 
                                b.A <- b.A + d.A.[(d.Length - b.Length)..]
                                pushRec ((bx DVector.Zero b) :: t)
                            | Split_DV(a, i) -> 
                                a.A <- DVector.AddSubVector(a.A, i, d.A)
                                pushRec ((bx DVector.Zero a) :: t)
                            | AddItem_DV_D(a, i, b) -> pushRec ((bx d.A a) :: (bx (d.A.[i]) b) :: t)
                            | AddItem_DV_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | AddItem_DVCons_D(i, b) -> pushRec ((bx d.A.[i] b) :: t)
                            | AddSubVector_DV_DV(a, i, b) -> 
                                pushRec ((bx d.A a) :: (bx (d.A.[i..(i + b.Length - 1)]) b) :: t)
                            | AddSubVector_DV_DVCons(a) -> pushRec ((bx d.A a) :: t)
                            | AddSubVector_DVCons_DV(i, b) -> pushRec ((bx (d.A.[i..(i + b.Length - 1)]) b) :: t)
                            | ReshapeCopy_DM_DV(a) -> pushRec ((bx (DVector.ReshapeToDM(a.Rows, d.A)) a) :: t)
                            | Slice_DV(a, i) -> 
                                a.A <- DVector.AddSubVector(a.A, i, d.A)
                                pushRec ((bx DVector.Zero a) :: t)
                            | Diagonal_DM(a) -> 
                                a.A <- DNDArray.AddDiagonal(a.A, d.A)
                                pushRec ((bx DNDArray.Zero a) :: t)
                            | ReLU_DV(a) -> pushRec ((bx (d.A .* ((DVector.Sign(a.P) + number1) / number2)) a) :: t)
                            | Sigmoid_DV(a) -> pushRec ((bx (d.A .* d.P .* (number1 - d.P)) a) :: t) // d.P = DV.Sigmoid(a.P)
                            | _ -> pushRec t
                        else pushRec t
                    | _ -> pushRec t
                | :? DNDArray as d -> 
                    match d with
                    | DMR(_, _, o, _, _) -> 
                        d.A <- d.A + (v :?> DNDArray)
                        d.F <- d.F - 1u
                        if d.F = 0u then 
                            match o with
                            | Add_DM_DM(a, b) -> pushRec ((bx d.A a) :: (bx d.A b) :: t)
                            | Add_DM_DMCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DM_DM(a, b) -> pushRec ((bx d.A a) :: (bx -d.A b) :: t)
                            | Sub_DM_DMCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DMCons_DM(a) -> pushRec ((bx -d.A a) :: t)
                            | Mul_DM_DM(a, b) -> 
                                pushRec 
                                    ((bx (d.A * DNDArray.Transpose(b.P)) a) 
                                     :: (bx (DNDArray.Transpose(a.P) * d.A) b) :: t)
                            | Mul_DM_DMCons(a, cons) -> pushRec ((bx (d.A * DNDArray.Transpose(cons)) a) :: t)
                            | Mul_DMCons_DM(cons, b) -> pushRec ((bx (DNDArray.Transpose(cons) * d.A) b) :: t)
                            | Mul_Had_DM_DM(a, b) -> pushRec ((bx (d.A .* b.P) a) :: (bx (d.A .* a.P) b) :: t)
                            | Mul_Had_DM_DMCons(a, cons) -> pushRec ((bx (d.A .* cons) a) :: t)
                            | Mul_DM_D(a, b) -> pushRec ((bx (d.A * b.P) a) :: (bx (DNDArray.Sum(d.A .* a.P)) b) :: t)
                            | Mul_DM_DCons(a, cons) -> pushRec ((bx (d.A * cons) a) :: t)
                            | Mul_DMCons_D(cons, b) -> pushRec ((bx (DNDArray.Sum(d.A .* cons)) b) :: t)
                            | Mul_Out_DV_DV(a, b) -> 
                                pushRec ((bx (d.A * b.P) a) :: (bx (DNDArray.Transpose(d.A) * a.P) b) :: t)
                            | Mul_Out_DV_DVCons(a, cons) -> pushRec ((bx (d.A * cons) a) :: t)
                            | Mul_Out_DVCons_DV(cons, b) -> pushRec ((bx (DNDArray.Transpose(d.A) * cons) b) :: t)
                            | Div_Had_DM_DM(a, b) -> 
                                pushRec ((bx (d.A ./ b.P) a) :: (bx (d.A .* (-a.P ./ (b.P .* b.P))) b) :: t)
                            | Div_Had_DM_DMCons(a, cons) -> pushRec ((bx (d.A ./ cons) a) :: t)
                            | Div_Had_DMCons_DM(cons, b) -> pushRec ((bx (d.A .* (-cons ./ (b.P .* b.P))) b) :: t)
                            | Pow_DM_DM(a, b) -> 
                                pushRec 
                                    ((bx (d.A .* (a.P ** (b.P - D number1)) .* b.P) a) 
                                     :: (bx (d.A .* (a.P ** b.P) .* log a.P) b) :: t)
                            | Pow_DM_DMCons(a, cons) -> 
                                pushRec ((bx (d.A .* (a.P ** (cons - D number1)) .* cons) a) :: t)
                            | Pow_DMCons_DM(cons, b) -> pushRec ((bx (d.A .* (cons ** b.P) .* log cons) b) :: t)
                            | Atan2_DM_DM(a, b) -> 
                                let denom = (a.P .* a.P) + (b.P .* b.P)
                                pushRec ((bx (d.A .* b.P ./ denom) a) :: (bx (d.A .* (-a.P) ./ denom) b) :: t)
                            | Atan2_DM_DMCons(a, cons) -> 
                                pushRec ((bx (d.A .* cons ./ ((a.P .* a.P) + (cons .* cons))) a) :: t)
                            | Atan2_DMCons_DM(cons, b) -> 
                                pushRec ((bx (d.A .* (-cons) ./ ((cons .* cons) + (b.P .* b.P))) b) :: t)
                            | Add_DM_D(a, b) -> pushRec ((bx d.A a) :: (bx (DNDArray.Sum(d.A)) b) :: t)
                            | Add_DM_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Add_DMCons_D(b) -> pushRec ((bx (DNDArray.Sum(d.A)) b) :: t)
                            | Sub_DM_D(a, b) -> pushRec ((bx d.A a) :: (bx -(DNDArray.Sum(d.A)) b) :: t)
                            | Sub_DM_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | Sub_DMCons_D(b) -> pushRec ((bx -(DNDArray.Sum(d.A)) b) :: t)
                            | Sub_D_DM(a, b) -> pushRec ((bx (DNDArray.Sum(d.A)) a) :: (bx -d.A b) :: t)
                            | Sub_D_DMCons(a) -> pushRec ((bx (DNDArray.Sum(d.A)) a) :: t)
                            | Sub_DCons_DM(b) -> pushRec ((bx -d.A b) :: t)
                            | Div_DM_D(a, b) -> pushRec ((bx (d.A / b.P) a) :: (bx (d.A * (-a.P / (b.P * b.P))) b) :: t)
                            | Div_DM_DCons(a, cons) -> pushRec ((bx (d.A / cons) a) :: t)
                            | Div_DMCons_D(cons, b) -> pushRec ((bx (d.A * (-cons / (b.P * b.P))) b) :: t)
                            | Div_D_DM(a, b) -> 
                                pushRec 
                                    ((bx (DNDArray.Sum(d.A ./ b.P)) a) :: (bx (d.A .* (-a.P / (b.P .* b.P))) b) :: t)
                            | Div_D_DMCons(a, cons) -> pushRec ((bx (DNDArray.Sum(d.A ./ cons)) a) :: t)
                            | Div_DCons_DM(cons, b) -> pushRec ((bx (d.A .* (-cons / (b.P .* b.P))) b) :: t)
                            | Pow_DM_D(a, b) -> 
                                pushRec 
                                    ((bx (d.A .* (a.P ** (b.P - D number1)) * b.P) a) 
                                     :: (bx (DNDArray.Sum(d.A .* (a.P ** b.P) .* log a.P)) b) :: t)
                            | Pow_DM_DCons(a, cons) -> pushRec ((bx (d.A .* (a.P ** (cons - D number1)) * cons) a) :: t)
                            | Pow_DMCons_D(cons, b) -> 
                                pushRec ((bx (DNDArray.Sum(d.A .* (cons ** b.P) .* log cons)) b) :: t)
                            | Pow_D_DM(a, b) -> 
                                pushRec 
                                    ((bx (DNDArray.Sum(d.A .* (DNDArray.Pow(a.P, b.P - D number1)) .* b.P)) a) 
                                     :: (bx (d.A .* (DNDArray.Pow(a.P, b.P)) * log a.P) b) :: t)
                            | Pow_D_DMCons(a, cons) -> 
                                pushRec 
                                    ((bx (DNDArray.Sum(d.A .* (DNDArray.Pow(a.P, cons - D number1)) .* cons)) a) :: t)
                            | Pow_DCons_DM(cons, b) -> 
                                pushRec ((bx (d.A .* (DNDArray.Pow(cons, b.P)) * log cons) b) :: t)
                            | Atan2_DM_D(a, b) -> 
                                let denom = (a.P .* a.P) + (b.P * b.P)
                                pushRec 
                                    ((bx (d.A * b.P ./ denom) a) :: (bx (DNDArray.Sum(d.A .* (-a.P) ./ denom)) b) :: t)
                            | Atan2_DM_DCons(a, cons) -> 
                                pushRec ((bx (d.A * cons ./ ((a.P .* a.P) + (cons * cons))) a) :: t)
                            | Atan2_DMCons_D(cons, b) -> 
                                pushRec ((bx (DNDArray.Sum(d.A .* (-cons) ./ ((cons .* cons) + (b.P * b.P)))) b) :: t)
                            | Atan2_D_DM(a, b) -> 
                                let denom = (a.P * a.P) + (b.P .* b.P)
                                pushRec 
                                    ((bx (DNDArray.Sum(d.A .* b.P ./ denom)) a) :: (bx (d.A * (-a.P) ./ denom) b) :: t)
                            | Atan2_D_DMCons(a, cons) -> 
                                pushRec ((bx (DNDArray.Sum(d.A .* cons ./ ((a.P * a.P) + (cons .* cons)))) a) :: t)
                            | Atan2_DCons_DM(cons, b) -> 
                                pushRec ((bx (d.A * (-cons) ./ ((cons * cons) + (b.P .* b.P))) b) :: t)
                            | Log_DM(a) -> pushRec ((bx (d.A ./ a.P) a) :: t)
                            | Log10_DM(a) -> pushRec ((bx (d.A ./ (a.P * log10Val())) a) :: t)
                            | Exp_DM(a) -> pushRec ((bx (d.A .* d.P) a) :: t) // d.P = exp a.P
                            | Sin_DM(a) -> pushRec ((bx (d.A .* cos a.P) a) :: t)
                            | Cos_DM(a) -> pushRec ((bx (-d.A .* sin a.P) a) :: t)
                            | Tan_DM(a) -> 
                                let seca = D number1 / cos a.P
                                pushRec ((bx (d.A .* seca .* seca) a) :: t)
                            | Neg_DM(a) -> pushRec ((bx -d.A a) :: t)
                            | Sqrt_DM(a) -> pushRec ((bx (d.A ./ (number2 * d.P)) a) :: t) // d.P = sqrt a.P
                            | Sinh_DM(a) -> pushRec ((bx (d.A .* cosh a.P) a) :: t)
                            | Cosh_DM(a) -> pushRec ((bx (d.A .* sinh a.P) a) :: t)
                            | Tanh_DM(a) -> 
                                let secha = D number1 / cosh a.P
                                pushRec ((bx (d.A .* secha .* secha) a) :: t)
                            | Asin_DM(a) -> pushRec ((bx (d.A ./ sqrt (D number1 - (a.P .* a.P))) a) :: t)
                            | Acos_DM(a) -> pushRec ((bx (-d.A ./ sqrt (D number1 - (a.P .* a.P))) a) :: t)
                            | Atan_DM(a) -> pushRec ((bx (d.A ./ (D number1 + (a.P .* a.P))) a) :: t)
                            | Abs_DM(a) -> pushRec ((bx (d.A .* DNDArray.Sign a.P) a) :: t)
                            | Sign_DM(a) -> pushRec ((bx DNDArray.Zero a) :: t)
                            | Floor_DM(a) -> pushRec ((bx DNDArray.Zero a) :: t)
                            | Ceil_DM(a) -> pushRec ((bx DNDArray.Zero a) :: t)
                            | Round_DM(a) -> pushRec ((bx DNDArray.Zero a) :: t)
                            | Transpose_DM(a) -> pushRec ((bx (DNDArray.Transpose(d.A)) a) :: t)
                            | Make_DM_ofDs(a) -> 
                                pushRec 
                                    (t 
                                     |> List.append 
                                            (List.map2 (fun v dd -> (bx v dd)) (d.A
                                                                                |> DM.toDV
                                                                                |> DV.toArray
                                                                                |> Array.toList) (a |> List.ofArray)))
                            | AddItem_DM_D(a, i, j, b) -> pushRec ((bx d.A a) :: (bx (d.A.[i, j]) b) :: t)
                            | AddItem_DM_DCons(a) -> pushRec ((bx d.A a) :: t)
                            | AddItem_DMCons_D(i, j, b) -> pushRec ((bx d.A.[i, j] b) :: t)
                            | AddDiagonal_DM_DV(a, b) -> pushRec ((bx d.A a) :: (bx (DNDArray.Diagonal(d.A)) b) :: t)
                            | AddDiagonal_DM_DVCons(a) -> pushRec ((bx d.A a) :: t)
                            | AddDiagonal_DMCons_DV(b) -> pushRec ((bx (DNDArray.Diagonal(d.A)) b) :: t)
                            | ReshapeCopy_DV_DM(a) -> pushRec ((bx (DNDArray.ReshapeToDV(d.A)) a) :: t)
                            | Inverse_DM(a) -> 
                                let dpt = DNDArray.Transpose(d.P)
                                pushRec ((bx (-dpt * d.A * dpt) a) :: t) // d.P = DM.Inverse(a.P)
                            | ReLU_DM(a) -> pushRec ((bx (d.A .* ((DNDArray.Sign(a.P) + number1) / number2)) a) :: t)
                            | Sigmoid_DM(a) -> pushRec ((bx (d.A .* d.P .* (number1 - d.P)) a) :: t) // d.P = DM.Sigmoid(a.P)
                            | _ -> pushRec t
                        else pushRec t
                    | _ -> pushRec t
                | _ -> pushRec t
        pushRec [ (v, d) ]
    
    /// Propagates the adjoint `v` backwards through the evaluation trace of `d`. The adjoints in the trace are reset before the push.
    let reverseProp (v : obj) (d : obj) = 
        d |> reverseReset
        d |> reversePush v

/// Forward and reverse differentiation operations module (automatically opened)
[<AutoOpen>]
module DiffOps = 
    /// Original value and first derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diff' f x = 
        x
        |> makeForward GlobalTagger.Next (D number1)
        |> f
        |> primalTangent
    
    /// First derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diff f x = diff' f x |> snd
    
    /// Second derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diff2 f x = diff (diff f) x
    
    /// Original value, first derivative, and second derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diff2'' f x = 
        let v, d = diff' f x
        let d2 = diff2 f x
        (v, d, d2)
    
    /// Original value and second derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diff2' f x = diff2'' f x |> fsttrd
    
    /// `n`-th derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diffn n f x = 
        if n < 0 then ErrorMessages.InvalidArgDiffn()
        elif n = 0 then x |> f
        else 
            let rec d n f = 
                match n with
                | 1 -> diff f
                | _ -> d (n - 1) (diff f)
            x |> d n f
    
    /// Original value and `n`-th derivative of a scalar-to-scalar function `f`, at point `x`. Forward AD.
    let inline diffn' n f x = (x |> f, diffn n f x)
    
    /// Original value and gradient of a vector-to-scalar function `f`, at point `x`. Reverse AD.
    let inline grad' f x = 
        let xa = x |> makeReverse GlobalTagger.Next
        let z : DNumber = f xa
        z |> reverseReset
        z |> reversePush (D number1)
        (z |> primal, xa |> adjoint)
    
    /// Gradient of a vector-to-scalar function `f`, at point `x`. Reverse AD.
    let inline grad f x = grad' f x |> snd
    
    /// Original value and Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`. Forward AD.
    let inline jacobianv' f x v = 
        x
        |> makeForward GlobalTagger.Next v
        |> f
        |> primalTangent
    
    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`. Forward AD.
    let inline jacobianv f x v = jacobianv' f x v |> snd
    
    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`. Forward AD.
    let inline gradv f x v = jacobianv f x v
    
    /// Original value and gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`. Forward AD.
    let inline gradv' f x v = jacobianv' f x v
    
    /// Original value and a function for evaluating the transposed Jacobian-vector product of a vector-to-vector function `f`, at point `x`. Of the returned pair, the first is the original value of function `f` at point `x` (the result of the forward pass of the reverse mode AD) and the second is a function (the reverse evaluator) that can compute the transposed Jacobian-vector product many times along many different vectors (performing a new reverse pass of reverse mode AD, with the given vector, without repeating the forward pass). Reverse AD.
    let inline jacobianTv'' (f : 'a -> 'b) (x : 'a) = 
        let xa = x |> makeReverse GlobalTagger.Next
        let z = f xa
        let r1 = z |> primal
        
        let r2 = 
            fun (v : 'b) -> 
                z |> reverseReset
                z |> reversePush v
                xa |> adjoint
        (r1, r2)
    
    /// Original value and transposed Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`. Reverse AD.
    let inline jacobianTv' f x v = 
        let r1, r2 = jacobianTv'' f x
        (r1, r2 v)
    
    /// Transposed Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`. Reverse AD.
    let inline jacobianTv f x v = jacobianTv' f x v |> snd
    
    /// Original value and Jacobian of a vector-to-vector function `f`, at point `x`. Forward or reverse AD, depending on input and output dimensions.
    let inline jacobian' f (x : DVector) = 
        let o : DVector = 
            x
            |> f
            |> primal
        if x.Length > o.Length then 
            let r = jacobianTv f x
            (o, Array.init o.Length (fun j -> r (DV.standardBasis o.Length j)) |> DM.ofRows)
        else (o, Array.init x.Length (fun i -> jacobianv f x (DV.standardBasis x.Length i)) |> DM.ofCols)
    
    /// Jacobian of a vector-to-vector function `f`, at point `x`. Forward or reverse AD, depending on input and output dimensions.
    let inline jacobian f x = jacobian' f x |> snd
    
    /// Original value and transposed Jacobian of a vector-to-vector function `f`, at point `x`. Forward or reverse AD, depending on input and output dimensions.
    let inline jacobianT' f x = jacobian' f x |> fun (r, j) -> (r, DM.transpose j)
    
    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`. Forward or reverse AD, depending on input and output dimensions.
    let inline jacobianT f x = jacobianT' f x |> snd
    
    /// Gradient and Hessian of a vector-to-scalar function `f`, at point `x`. Forward-on-reverse AD.
    let inline gradhessian f x = jacobian' (grad f) x
    
    /// Original value, gradient, and Hessian of a vector-to-scalar function `f`, at point `x`. Forward-on-reverse AD.
    let inline gradhessian' f x = 
        let g, h = gradhessian f x
        (x |> f, g, h)
    
    /// Hessian of a vector-to-scalar function `f`, at point `x`. Forward-on-reverse AD.
    let inline hessian f x = jacobian (grad f) x
    
    /// Original value and Hessian of a vector-to-scalar function `f`, at point `x`. Forward-on-reverse AD.
    let inline hessian' f x = (x |> f, hessian f x)
    
    /// Original value, gradient-vector product (directional derivative), and Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`. Reverse-on-forward AD.
    let inline gradhessianv' f x v = 
        let gv, hv = grad' (fun xx -> jacobianv f xx v) x
        (x |> f, gv, hv)
    
    /// Gradient-vector product (directional derivative) and Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`. Reverse-on-forward AD.
    let inline gradhessianv f x v = gradhessianv' f x v |> sndtrd
    
    /// Original value and Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`. Reverse-on-forward AD.
    let inline hessianv' f x v = gradhessianv' f x v |> fsttrd
    
    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`. Reverse-on-forward AD.
    let inline hessianv f x v = hessianv' f x v |> snd
    
    /// Original value and Laplacian of a vector-to-scalar function `f`, at point `x`. Reverse-on-forward AD.
    let inline laplacian' f x = // TODO: reimplement faster
        let v, h = hessian' f x
        (v, DM.trace h)
    
    /// Laplacian of a vector-to-scalar function `f`, at point `x`. Reverse-on-forward AD.
    let inline laplacian f x = laplacian' f x |> snd
    
    /// Original value and curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix. Forward AD.
    let inline curl' f x = 
        let v, j = jacobianT' f x
        if (j.Rows, j.Cols) <> (3, 3) then ErrorMessages.InvalidArgCurl()
        v, 
        toDV [| j.[1, 2] - j.[2, 1]
                j.[2, 0] - j.[0, 2]
                j.[0, 1] - j.[1, 0] |]
    
    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix. Forward AD.
    let inline curl f x = curl' f x |> snd
    
    /// Original value and divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix. Forward AD.
    let inline div' f x = 
        let v, j = jacobianT' f x
        if j.Rows <> j.Cols then ErrorMessages.InvalidArgDiv()
        v, DM.trace j
    
    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix. Forward AD.
    let inline div f x = div' f x |> snd
    
    /// Original value, curl, and divergence of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix. Forward AD.
    let inline curldiv' f x = 
        let v, j = jacobianT' f x
        if (j.Rows, j.Cols) <> (3, 3) then ErrorMessages.InvalidArgCurlDiv()
        v, 
        toDV [| j.[1, 2] - j.[2, 1]
                j.[2, 0] - j.[0, 2]
                j.[0, 1] - j.[1, 0] |], DM.trace j
    
    /// Curl and divergence of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix. Forward AD.
    let inline curldiv f x = curldiv' f x |> sndtrd
