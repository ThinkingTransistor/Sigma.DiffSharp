using System;
using DiffSharp;
using DiffSharp.AD;
using static DiffSharp.Interop.Float64.AD;
using DiffSharp.Interop.Float64;

namespace InteropTest
{
	public class Program
	{
		// Define a function whose derivative you need
		// F(x) = Sin(x^2 - Exp(x))
		public static DNumber F(DNumber x)
		{
			return Sin(x * x - Exp(x));
		}

		public static void Main(string[] args)
		{
			// You can compute the value of the derivative of F at a point
			DNumber f = Diff(F, 2.3);

			// Or, you can generate a derivative function which you may use for many evaluations
			// dF is the derivative function of F
			var dF = Diff(F);

			// Evaluate the derivative function at different points
			DNumber db = dF(2.3);
			DNumber dc = dF(1.4);

			Console.WriteLine(db);
			Console.WriteLine(dc);

			// Construction anDNumbercasting of DNumber(scalar) values
			// Construct new D
			DNumber a = new DNumber(4.1);
			// Cast double to D
			DNumber b = 4.1;
			// Cast DNumberto double
			double c = b;

			// Construction anDNumbercasting of DVector (vector) values
			// Construct new DVector
			DVector va = new DVector(new Util.DataBuffer<double>(new double[] { 1, 2, 3 }));
			// Cast double[] to DVector
			double[] vaa = new double[] { 1, 2, 3 };
			DVector vb = new Util.DataBuffer<double>(vaa);
			// Cast DVector to double[]

			Console.Write(va);

			//// Construction anDNumbercasting of DMatrix (matrix) values
			//// Construct new DMatrix
			//DMatrix ma = new DMatrix(new double[,] { { 1, 2 }, { 3, 4 } });
			//// Cast double[,] to DMatrix
			//double[,] maa = new double[,] { { 1, 2 }, { 3, 4 } };
			//DMatrix mb = maa;
			//// Cast DMatrix to double[,]
			//double[,] mc = mb;

			Console.ReadKey();
		}
	}

	public class NDArray : DNDArray
	{
		public NDArray(Float64.DNDArray m) : base(m)
		{
		}
	}
}
