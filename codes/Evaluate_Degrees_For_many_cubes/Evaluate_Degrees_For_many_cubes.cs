using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Gurobi;
using System.IO;

namespace Evaluate_Degrees_For_many_cubes
{
    class Program
    {
        static void Main(string[] args)
        {
            int round = 820 - 200;
            int termnum = 30;
            StreamReader manycubes = new StreamReader("manycubes.txt");

            for (int nn = 0; nn < 20; nn++)
            {
                string strtmp = manycubes.ReadLine();
                string[] mon = strtmp.Split(',');
                List<uint> curcube = new List<uint>();
                for (int i = 0; i < mon.Length; i++)
                    curcube.Add((uint)Convert.ToInt32(mon[i]));

                Console.Write("Cube("+ curcube.Count + "): ");
                for (int i = 0; i < curcube.Count; i++)
                    Console.Write(curcube[i] + ",");
                Console.WriteLine();

                int maxdeg = -1;
                int NO = 0;
                int curdeg = 0;
                StreamReader terms = new StreamReader("terms.txt");
                for (int m = 0; m < termnum; m++)
                {
                    string strtmp2 = terms.ReadLine();
                    string[] mon2 = strtmp2.Split(',');
                    int[] pos = new int[mon2.Length];
                    for (int i = 0; i < mon2.Length; i++)
                    {
                        pos[i] = Convert.ToInt32(mon2[i]);
                    }
                    GRBEnv env = new GRBEnv("Trvium.log");
                    GRBModel model = new GRBModel(env);  

                    model.Parameters.LogToConsole = 0;   

                    GRBVar[] IV = model.AddVars(80, GRB.BINARY);  
                    GRBVar[] Key = model.AddVars(80, GRB.BINARY);
                    for (int i = 0; i < 80; i++)
                    {
                        IV[i].VarName = "IV" + i.ToString(); 
                        Key[i].VarName = "Key" + i.ToString(); 
                    }
                    GRBVar[] s = model.AddVars(288, GRB.BINARY);
                    for (int i = 0; i < 288; i++)
                        s[i].VarName = "var" + i.ToString();

                    char[] FlagS = new char[288];

                    GRBVar[] NewVars = model.AddVars(30 * round, GRB.BINARY);
                    for (int i = 0; i < NewVars.Length; i++)
                        NewVars[i].VarName = "y" + i.ToString();
                    char[] FlagNewVars = new char[30 * round];

                    List<uint> ivbits_set_to_1 = new List<uint>() { };  //Iv bits set to 1
                    List<uint> ivbits_set_to_0 = new List<uint>() { };  //Iv bits set to 0
                    for (uint i = 0; i < 80; i++)
                        ivbits_set_to_0.Add(i);
                    for (int i = 0; i < curcube.Count; i++)
                    {
                        ivbits_set_to_0.Remove(curcube[i]);
                    }

                    List<UInt32> Noncube = new List<uint>() { 0x0, 0x0, 0x0 };//Noncube stores the value of the non-cube variables

                    //for each iv bit which is set to 1, set the corresponding bit of Noncube to 1.
                    for (int i = 0; i < ivbits_set_to_1.Count; i++)
                    {
                        Noncube[(int)ivbits_set_to_1[i] >> 5] |= (uint)(0x01 << ((int)(ivbits_set_to_1[i] & 0x1f)));
                    }

                    GRBLinExpr ChooseIV = new GRBLinExpr();   //
                    for (int i = 0; i < curcube.Count; i++)
                        ChooseIV.AddTerm(1.0, IV[curcube[i]]);

                    //the bits set to constants
                    List<int> chokey = new List<int>() { };

                    //pick up the key variables which are not fixed.
                    //i.e. keydeg= k_i1+k_i2+...+k_in, where k_i1,k_i2,...,k_im are the key bits which are not fixed
                    GRBLinExpr keydeg = new GRBLinExpr();
                    for (int i = 0; i < 80; i++)
                    {
                        if (!chokey.Contains(i))
                            keydeg.AddTerm(1.0, Key[i]);
                    }
                    if (curdeg != 0)
                        model.AddConstr(keydeg >= curdeg + 1, "New");
                                                                        //set maximizing the linear expression keydeg as the objective function of our model
                                                                        //Hence, we could obtain the upper bound of the degree of the superpoly of the chosen cube.
                                                                        //model.AddConstr(keydeg <= mini, "ConsOnMaxDeg");

                    model.SetObjective(keydeg, GRB.MAXIMIZE);

                    //in this function, we set the conditions which are imposed to the key bits and iv bits
                    //before running, it needs to set some parameters, such as the key bits set to 0/1 and so on, in this function,
                    initial(model, s, FlagS, curcube, Noncube, IV, Key);

                    int VarNumber = 0;

                    //describe the propagation of the division property with flag through Trivium
                    for (int i = 1; i <= round; i++)
                        Triviumcore(model, s, FlagS, NewVars, FlagNewVars, ref VarNumber);

                    for (int i = 0; i < 288; i++)
                    {
                        if (pos.Contains(i))
                        {
                            model.AddConstr(s[i] == 1, "1");
                        }
                        else
                        {
                            model.AddConstr(s[i] == 0, "1");
                        }
                    }

                    model.Optimize();  //solve the MILP model.

                    int currentdeg;

                    //outout the solution

                    // is the model is feasible the upper bound of the degree of the superpoly is large than 0.
                    // In this case, we output a possible term of degree d, where d is the upper bound of the degree of the superpoly.
                    if (model.SolCount > 0)
                    {
                        //StreamWriter MaxDegT = new StreamWriter("MaxdegreeTerms.txt", true);
                        currentdeg = (int)model.ObjVal;   //Model objective function value
                        NO++;
                        Console.WriteLine("****************No." + NO + "********************");
                        for (int ii = 0; ii < pos.Length; ii++)
                        {
                            Console.Write(pos[ii] + ",");
                        }
                        Console.WriteLine("  " + currentdeg);
                        if (currentdeg >= maxdeg)
                        {
                            maxdeg = currentdeg;
                        }
                        if (currentdeg > 9)     //Reject high-degree Cube  
                        {
                            break;
                        }
                        curdeg = maxdeg;
                    }
                    else//if the model is imfeasible, then the degree of the superpoly is upper bounded by 0.
                    {
                        currentdeg = 0;
                        if (currentdeg >= maxdeg)
                        {
                            maxdeg = currentdeg;
                        }
                    }
                    model.Dispose();
                    env.Dispose();

                }
                
                Console.WriteLine(maxdeg);
                Console.Write("\n***********************************************\n");
                Console.WriteLine();

                if (maxdeg < 10)  
                {
                    StreamWriter MaxDegT = new StreamWriter("MaxdegreeTerms.txt", true);
                    MaxDegT.WriteLine("*****************round" + (round + 200) + "**********************");
                    for (int i = 0; i < curcube.Count; i++)
                    {
                        MaxDegT.Write(curcube[i] + ",");
                    }
                    MaxDegT.WriteLine();
                    MaxDegT.Write("Upper bound of degree of superpoly: ");
                    MaxDegT.WriteLine(maxdeg);
                    MaxDegT.WriteLine();
                    MaxDegT.Close();
                }
                terms.Close();
            }
            manycubes.Close();
            Console.ReadLine();







            //initialize the model and set the conditions imposed to the key/iv bits.
            static void initial(GRBModel model, GRBVar[] s, char[] FlagS, List<uint> cube, List<UInt32> Noncube, GRBVar[] IV, GRBVar[] Key)
            {
                //key bits set to 0
                List<int> chosenkey = new List<int>() { };
                //key bits set to 1
                List<int> onekey = new List<int>() { };
                for (int i = 0; i < 80; i++)
                {
                    //set key bits in chosenkey to constant 0
                    if (chosenkey.Contains(i))
                    {
                        model.AddConstr(s[i] == 0, "z" + i.ToString());
                        FlagS[i] = '0';
                    }
                    else
                    {
                        //set the key bits in onekey to constant 1
                        if (onekey.Contains(i))
                        {
                            Console.WriteLine("******" + i + "********");
                            model.AddConstr(s[i] == 0, "z" + i.ToString());
                            FlagS[i] = '1';
                        }
                        else// treat the remaining key bits as variables.
                        {
                            model.AddConstr(s[i] == Key[i], "z" + i.ToString());
                            FlagS[i] = '2';
                        }
                    }
                }

                for (int i = 80; i < 93; i++)
                {
                    model.AddConstr(s[i] == 0, "z" + i.ToString());
                    FlagS[i] = '0';
                }


                if (Noncube.Count == 0)//if the noncube variables are not set to constants
                {
                    for (uint i = 93; i < 173; i++)
                    {

                        if (cube.Contains(i - 93))
                        {
                            model.AddConstr(s[i] == 1, "IV" + i.ToString());
                        }
                        else
                        {
                            model.AddConstr(s[i] == 0, "z" + i.ToString());
                        }
                        FlagS[i] = '2';
                    }
                }
                else//if the non-cube variables are set to constants
                {
                    for (uint i = 93; i < 173; i++)
                    {
                        //treat the iv bits in cube as variable
                        if (cube.Contains(i - 93))
                        {
                            model.AddConstr(s[i] == 1, "z" + i.ToString());
                            FlagS[i] = '2';
                        }
                        else
                        {
                            //model.AddConstr(IV[i - 93] == 0, "IV" + i.ToString());
                            model.AddConstr(s[i] == 0, "z" + i.ToString());
                            int pos1 = (int)((i - 93) >> 5);
                            int pos2 = (int)(((i - 93) & 0x1f));
                            //the flag of iv bits which are set to 1 is set to '1'
                            if (((Noncube[pos1] >> pos2) & 0x01) == 1)
                            {
                                FlagS[i] = '1';
                            }
                            else //the flag of iv bits which are set to 0 is set to '0'
                            {
                                FlagS[i] = '0';
                            }
                        }
                    }
                }
                //initialize the state bits which are loaded with constants
                //namely, set the last 4 bits of the second register and the first 108 bits in the third register to constant 0
                //set the last 3 bits of the third register to 1.
                for (int i = 173; i < 285; i++)
                {
                    model.AddConstr(s[i] == 0, "z" + i.ToString());
                    FlagS[i] = '0';
                }
                for (int i = 285; i < 288; i++)
                {
                    model.AddConstr(s[i] == 0, "z" + i.ToString());
                    FlagS[i] = '1';
                }

            }

            //describe the propagation of division property through the round function of Trivium
            static void Triviumcore(GRBModel model, GRBVar[] s, Char[] FlagS, GRBVar[] NewVar, char[] FlagNewVar, ref int VarNumber)
            {
                int[] posA = new int[5] { 65, 170, 90, 91, 92 };
                for (int i = 0; i < 4; i++)
                {
                    model.AddConstr(NewVar[VarNumber + 2 * i] + NewVar[VarNumber + 2 * i + 1] == s[posA[i]], "c" + (VarNumber + i).ToString());
                    FlagNewVar[VarNumber + 2 * i] = FlagS[posA[i]];
                    FlagNewVar[VarNumber + 2 * i + 1] = FlagS[posA[i]];
                }
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 5], "c" + (VarNumber + 5).ToString());
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 7], "c" + (VarNumber + 6).ToString());
                FlagNewVar[VarNumber + 8] = FlagMul(FlagNewVar[VarNumber + 5], FlagNewVar[VarNumber + 7]);
                if (FlagNewVar[VarNumber + 8] == '0')
                    model.AddConstr(NewVar[VarNumber + 8] == 0, "t" + (VarNumber / 10).ToString());
                model.AddConstr(NewVar[VarNumber + 9] == s[posA[4]] + NewVar[VarNumber + 8] + NewVar[VarNumber + 1] + NewVar[VarNumber + 3], "c" + (VarNumber + 7).ToString());
                FlagNewVar[VarNumber + 9] = FlagAdd(FlagAdd(FlagS[posA[4]], FlagNewVar[VarNumber + 8]), FlagAdd(FlagNewVar[VarNumber + 1], FlagNewVar[VarNumber + 3]));
                VarNumber = VarNumber + 10;

                int[] posB = new int[5] { 161, 263, 174, 175, 176 };
                for (int i = 0; i < 4; i++)
                {
                    model.AddConstr(NewVar[VarNumber + 2 * i] + NewVar[VarNumber + 2 * i + 1] == s[posB[i]], "c" + (VarNumber + i).ToString());
                    FlagNewVar[VarNumber + 2 * i] = FlagS[posB[i]];
                    FlagNewVar[VarNumber + 2 * i + 1] = FlagS[posB[i]];
                }
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 5], "c" + (VarNumber + 5).ToString());
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 7], "c" + (VarNumber + 6).ToString());
                FlagNewVar[VarNumber + 8] = FlagMul(FlagNewVar[VarNumber + 5], FlagNewVar[VarNumber + 7]);
                if (FlagNewVar[VarNumber + 8] == '0')
                    model.AddConstr(NewVar[VarNumber + 8] == 0, "t" + (VarNumber / 10).ToString());
                model.AddConstr(NewVar[VarNumber + 9] == s[posB[4]] + NewVar[VarNumber + 8] + NewVar[VarNumber + 1] + NewVar[VarNumber + 3], "c" + (VarNumber + 7).ToString());
                FlagNewVar[VarNumber + 9] = FlagAdd(FlagAdd(FlagS[posB[4]], FlagNewVar[VarNumber + 8]), FlagAdd(FlagNewVar[VarNumber + 1], FlagNewVar[VarNumber + 3]));
                VarNumber = VarNumber + 10;

                int[] posC = new int[5] { 242, 68, 285, 286, 287 };
                for (int i = 0; i < 4; i++)
                {
                    model.AddConstr(NewVar[VarNumber + 2 * i] + NewVar[VarNumber + 2 * i + 1] == s[posC[i]], "c" + (VarNumber + i).ToString());
                    FlagNewVar[VarNumber + 2 * i] = FlagS[posC[i]];
                    FlagNewVar[VarNumber + 2 * i + 1] = FlagS[posC[i]];
                }
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 5], "c" + (VarNumber + 5).ToString());
                model.AddConstr(NewVar[VarNumber + 8] >= NewVar[VarNumber + 7], "c" + (VarNumber + 6).ToString());
                FlagNewVar[VarNumber + 8] = FlagMul(FlagNewVar[VarNumber + 5], FlagNewVar[VarNumber + 7]);
                if (FlagNewVar[VarNumber + 8] == '0')
                    model.AddConstr(NewVar[VarNumber + 8] == 0, "t" + (VarNumber / 10).ToString());
                model.AddConstr(NewVar[VarNumber + 9] == s[posC[4]] + NewVar[VarNumber + 8] + NewVar[VarNumber + 1] + NewVar[VarNumber + 3], "c" + (VarNumber + 7).ToString());
                FlagNewVar[VarNumber + 9] = FlagAdd(FlagAdd(FlagS[posC[4]], FlagNewVar[VarNumber + 8]), FlagAdd(FlagNewVar[VarNumber + 1], FlagNewVar[VarNumber + 3]));
                VarNumber = VarNumber + 10;

                for (int i = 287; i > 0; i--)
                {
                    s[i] = s[i - 1];
                    FlagS[i] = FlagS[i - 1];
                }
                s[0] = NewVar[VarNumber - 10 + 9]; FlagS[0] = FlagNewVar[VarNumber - 10 + 9];
                s[287] = NewVar[VarNumber - 10 + 6]; FlagS[287] = FlagNewVar[VarNumber - 10 + 6];
                s[286] = NewVar[VarNumber - 10 + 4]; FlagS[286] = FlagNewVar[VarNumber - 10 + 4];
                s[69] = NewVar[VarNumber - 10 + 2]; FlagS[69] = FlagNewVar[VarNumber - 10 + 2];
                s[243] = NewVar[VarNumber - 10 + 0]; FlagS[243] = FlagNewVar[VarNumber - 10 + 0];
                s[177] = NewVar[VarNumber - 20 + 9]; FlagS[177] = FlagNewVar[VarNumber - 20 + 9];
                s[176] = NewVar[VarNumber - 20 + 6]; FlagS[176] = FlagNewVar[VarNumber - 20 + 6];
                s[175] = NewVar[VarNumber - 20 + 4]; FlagS[175] = FlagNewVar[VarNumber - 20 + 4];
                s[264] = NewVar[VarNumber - 20 + 2]; FlagS[264] = FlagNewVar[VarNumber - 20 + 2];
                s[162] = NewVar[VarNumber - 20 + 0]; FlagS[162] = FlagNewVar[VarNumber - 20 + 0];
                s[93] = NewVar[VarNumber - 30 + 9]; FlagS[93] = FlagNewVar[VarNumber - 30 + 9];
                s[92] = NewVar[VarNumber - 30 + 6]; FlagS[92] = FlagNewVar[VarNumber - 30 + 6];
                s[91] = NewVar[VarNumber - 30 + 4]; FlagS[91] = FlagNewVar[VarNumber - 30 + 4];
                s[171] = NewVar[VarNumber - 30 + 2]; FlagS[171] = FlagNewVar[VarNumber - 30 + 2];
                s[66] = NewVar[VarNumber - 30 + 0]; FlagS[66] = FlagNewVar[VarNumber - 30 + 0];
            }

            //propagation rule on the XOR operation  of flag 
            static char FlagAdd(char FlagA, char FlagB)
            {
                if (FlagA == '0')
                {
                    return FlagB;
                }
                else if (FlagA == '1')
                {
                    if (FlagB == '0')
                        return FlagA;
                    else if (FlagB == '1')
                        return '0';
                    else
                        return '2';
                }
                else
                {
                    return '2';
                }

            }

            //propagation rule on the AND operation of flag 
            static char FlagMul(char FlagA, char FlagB)
            {
                if (FlagA == '0')
                {
                    return '0';
                }
                else if (FlagA == '1')
                {
                    return FlagB;
                }
                else
                {
                    if (FlagB == '0')
                        return '0';
                    else
                        return FlagA;
                }
            }

        }

    }

}
