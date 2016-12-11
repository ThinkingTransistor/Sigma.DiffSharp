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


/// Numerical differentiation module
module DiffSharp.Numerical.Float64

open DiffSharp.Util
open DiffSharp.Config

type number = float
type IDataBuffer = IDataBuffer<number>

let inline FixedPointEpsilon     () = global.DiffSharp.Config.GlobalConfig.Float64FixedPointEpsilon
let inline FixedPointEpsilonRec  () = global.DiffSharp.Config.GlobalConfig.Float64EpsilonRec
let inline FixedPointEpsilonRec2 () = global.DiffSharp.Config.GlobalConfig.Float64EpsilonRec2
let inline log10Val              () = log10ValFloat64

/// Numerical differentiation operations module (automatically opened)
[<AutoOpen>]
module DiffOps =
    open DiffSharp.Backend

    /// First derivative of a scalar-to-scalar function `f`, at point `x`
    let inline diff (f:number->number) x =
        ((f (x + FixedPointEpsilon())) - (f (x - FixedPointEpsilon()))) * FixedPointEpsilonRec2()
    
    /// Original value and first derivative of a scalar-to-scalar function `f`, at point `x`
    let inline diff' f x =
        (f x, diff f x)

    /// Gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
    let inline gradv (f:IDataBuffer->number) (x:IDataBuffer) (v:IDataBuffer) (backend:Backend<number>) =
        let veps = backend.Mul_S_V(FixedPointEpsilon(), v)
        ((f (backend.Add_V_V(x, veps))) - (f (backend.Sub_V_V(x, veps)))) * FixedPointEpsilonRec2()

    /// Original value and gradient-vector product (directional derivative) of a vector-to-scalar function `f`, at point `x`, along vector `v`
    let inline gradv' f x v (backend:Backend<number>) =
        (f x, gradv f x v)

    /// Second derivative of a scalar-to-scalar function `f`, at point `x`
    let inline diff2 f x (backend:Backend<number>) =
        ((f (x + FixedPointEpsilon())) - 2. * (f x) + (f (x - FixedPointEpsilon()))) / (FixedPointEpsilon() * FixedPointEpsilon())

    /// Original value and second derivative of a scalar-to-scalar function `f`, at point `x`
    let inline diff2' f x (backend:Backend<number>) =
        (f x, diff2 f x)

    /// Original value, first derivative, and second derivative of a scalar-to-scalar function `f`, at point `x`
    let inline diff2'' f x (backend:Backend<number>) =
        (f x, diff f x, diff2 f x)

    /// Original value and gradient of a vector-to-scalar function `f`, at point `x`
    let inline grad' (f:IDataBuffer->number) x (backend:Backend<number>) =
        let fx = f x
        let g = NativeDataBuffer<number>(Array.create x.Length fx)
        let gg = NativeDataBuffer<number>(Array.init x.Length (fun i -> f (backend.Add_V_V(x, NativeDataBuffer<number>(standardBasisVal x.Length i (FixedPointEpsilon()))))))
        (fx, backend.Mul_S_V(FixedPointEpsilonRec(), backend.Sub_V_V(gg, g)))
    
    /// Gradient of a vector-to-scalar function `f`, at point `x`
    let grad f x (backend:Backend<number>) =
        grad' f x backend |> snd

    /// Original value, gradient, and Hessian of a vector-to-scalar function `f`, at point `x`
    let inline gradhessian' f x (backend:Backend<number>) =
        let (fx, g) = grad' f x backend
        let h = ShapedDataBufferView(NativeDataBuffer<number>((Array.create x.Length (Array.toSeq g.SubData)) |> Seq.concat |> Seq.toArray), int64 x.Length, int64 x.Length)
        let hh = ShapedDataBufferView((Array.init x.Length (fun i -> Array.toSeq((grad f (backend.Add_V_V(x, NativeDataBuffer<number>(standardBasisVal x.Length i (FixedPointEpsilon())))) backend).SubData))) |> Seq.concat |> Seq.toArray |> NativeDataBuffer<number>, int64 x.Length, int64 x.Length)
        (fx, g, backend.Mul_S_M(FixedPointEpsilonRec(), backend.Sub_M_M(hh, h)))

    /// Gradient and Hessian of a vector-to-scalar function `f`, at point `x`
    let inline gradhessian f x (backend:Backend<number>) =
        gradhessian' f x backend |> sndtrd

    /// Original value and Hessian of a vector-to-scalar function `f`, at point `x`
    let inline hessian' f x (backend:Backend<number>) =
        gradhessian' f x backend |> fsttrd
                
    /// Hessian of a vector-to-scalar function `f`, at point `x`
    let inline hessian f x (backend:Backend<number>) =
        gradhessian' f x backend |> trd

    /// Original value and Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`
    let inline hessianv' (f:IDataBuffer->number) (x:IDataBuffer) (v:IDataBuffer) (backend:Backend<number>) =
        let veps = backend.Mul_S_V(FixedPointEpsilon(), v)
        let fx, gg1 = grad' f (backend.Add_V_V(x, veps)) backend
        let gg2 = grad f (backend.Sub_V_V(x, veps)) backend
        (fx, backend.Mul_S_V(FixedPointEpsilonRec2(), backend.Sub_V_V(gg1, gg2)))

    /// Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`
    let inline hessianv (f:IDataBuffer->number) x v (backend:Backend<number>) =
        hessianv' f x v backend |> snd

    /// Original value, gradient-vector product (directional derivative), and Hessian-vector product of a vector-to-scalar funtion `f`, at point `x`, along vector `v`
    let inline gradhessianv' (f:IDataBuffer->number) x v (backend:Backend<number>) =
        let fx, gv = gradv' f x v backend
        let hv = hessianv f x v backend
        (fx, gv, hv)

    /// Gradient-vector product (directional derivative) and Hessian-vector product of a vector-to-scalar function `f`, at point `x`, along vector `v`
    let inline gradhessianv (f:IDataBuffer->number) x v (backend:Backend<number>) =
        gradhessianv' f x v backend |> sndtrd

    /// Original value and Laplacian of a vector-to-scalar function `f`, at point `x`
    let inline laplacian' f x (backend:Backend<number>) =
        let (v, h) = hessian' f x backend in (v, backend.Sum_V(backend.Diagonal_M(h)))

    /// Laplacian of a vector-to-scalar function `f`, at point `x`
    let inline laplacian f x (backend:Backend<number>) =
        laplacian' f x backend |> snd

    /// Original value and transposed Jacobian of a vector-to-vector function `f`, at point `x`
    let inline jacobianT' (f:IDataBuffer->IDataBuffer) x (backend:Backend<number>) =
        let fx = f x
        let j = ShapedDataBufferView<number>(NativeDataBuffer<number>((Array.create x.Length (Array.toSeq fx.SubData)) |> Seq.concat |> Seq.toArray), int64 x.Length, int64 x.Length)
        let jj = ShapedDataBufferView<number>(Array.init x.Length (fun i -> Array.toSeq((f (backend.Add_V_V(x, NativeDataBuffer<number>(standardBasisVal x.Length i (FixedPointEpsilon()))))).SubData)) |> Seq.concat |> Seq.toArray |> NativeDataBuffer<number>, int64 x.Length, int64 x.Length)
        (fx, backend.Mul_S_M(FixedPointEpsilonRec(), backend.Sub_M_M(jj, j)))

    /// Transposed Jacobian of a vector-to-vector function `f`, at point `x`
    let inline jacobianT f x (backend:Backend<number>) =
        jacobianT' f x backend |> snd

    /// Original value and Jacobian of a vector-to-vector function `f`, at point `x`
    let inline jacobian' f x (backend:Backend<number>) =
        jacobianT' f x backend |> fun (r, j) -> (r, backend.Transpose_M(j))

    /// Jacobian of a vector-to-vector function `f`, at point `x`
    let inline jacobian f x (backend:Backend<number>) =
        jacobian' f x backend |> snd

    /// Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    let inline jacobianv (f:IDataBuffer->IDataBuffer) x v (backend:Backend<number>) =
        let veps = backend.Mul_S_V(FixedPointEpsilon(), v)
        backend.Mul_S_V(FixedPointEpsilonRec2(), backend.Sub_V_V(f (backend.Add_V_V(x, veps)), f (backend.Sub_V_V(x, veps))))

    /// Original value and Jacobian-vector product of a vector-to-vector function `f`, at point `x`, along vector `v`
    let inline jacobianv' f x v (backend:Backend<number>) =
        (f x, jacobianv f x v)

    /// Original value and curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    let inline curl' f x (backend:Backend<number>) =
        let v, j = jacobianT' f x backend
        if (j.Rows, j.Cols) <> (3, 3) then ErrorMessages.InvalidArgCurl()
        v, [|j.[1, 2] - j.[2, 1]; j.[2, 0] - j.[0, 2]; j.[0, 1] - j.[1, 0]|]

    /// Curl of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    let inline curl f x (backend:Backend<number>) =
        curl' f x backend |> snd

    /// Original value and divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
    let inline div' f x (backend:Backend<number>) =
        let v, j = jacobianT' f x backend
        if (j.Rows <> j.Cols) then ErrorMessages.InvalidArgDiv()
        v, backend.Sum_V(backend.Diagonal_M(j))

    /// Divergence of a vector-to-vector function `f`, at point `x`. Defined only for functions with a square Jacobian matrix.
    let inline div f x (backend:Backend<number>) =
        div' f x backend |> snd

    /// Original value, curl, and divergence of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    let inline curldiv' f x (backend:Backend<number>) =
        let v, j = jacobianT' f x backend
        if (j.Rows, j.Cols) <> (3, 3) then ErrorMessages.InvalidArgCurlDiv()
        v, [|j.[1, 2] - j.[2, 1]; j.[2, 0] - j.[0, 2]; j.[0, 1] - j.[1, 0]|], j.[0, 0] + j.[1, 1] + j.[2, 2]

    /// Curl and divergence of a vector-to-vector function `f`, at point `x`. Supported only for functions with a three-by-three Jacobian matrix.
    let inline curldiv f x (backend:Backend<number>) =
        curldiv' f x backend |> sndtrd

