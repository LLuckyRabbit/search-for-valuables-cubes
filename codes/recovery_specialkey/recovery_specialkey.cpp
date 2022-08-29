#include "gurobi_c++.h"
#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <string.h>
#include <bitset>
#include <algorithm>
#include <map>
#include <iomanip>
#include <cmath>
#include <ctime>
using namespace std;
vector<bitset<80>> special_keys;
int pattern;
int FLAG;

//Regard two 288-bit vectors a and b as ordinary integers and compare them to see whether a<b
struct cmpBitset288
{
    bool operator()(const bitset<288>& a, const bitset<288>& b) const {
        if (a.count() > b.count())
            return true;
        else if (a.count() < b.count())
            return false;
        for (int i = 0; i < 288; i++)
            if (a[i] > b[i])
                return true;
            else if (a[i] < b[i])
                return false;
        return false;
    }
};

struct twoStage
{
    bool useTwoStage;
    int divRound;
    vector<bitset<288>> hint;
};

void triviumCoreThree(GRBModel& model, vector<GRBVar>& x, int i1, int i2, int i3, int i4, int i5) {

    GRBVar y1 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar y2 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar y3 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar y4 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar y5 = model.addVar(0, 1, 0, GRB_BINARY);

    GRBVar z1 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar z2 = model.addVar(0, 1, 0, GRB_BINARY);
    GRBVar a = model.addVar(0, 1, 0, GRB_BINARY);

    model.addConstr(y1 <= x[i1]);
    model.addConstr(z1 <= x[i1]);
    model.addConstr(y1 + z1 >= x[i1]);

    model.addConstr(y2 <= x[i2]);
    model.addConstr(z2 <= x[i2]);
    model.addConstr(y2 + z2 >= x[i2]);

    model.addConstr(y3 <= x[i3]);
    model.addConstr(a <= x[i3]);
    model.addConstr(y3 + a >= x[i3]);

    model.addConstr(y4 <= x[i4]);
    model.addConstr(a <= x[i4]);
    model.addConstr(y4 + a >= x[i4]);

    model.addConstr(y5 == x[i5] + a + z1 + z2);

    x[i1] = y1;
    x[i2] = y2;
    x[i3] = y3;
    x[i4] = y4;
    x[i5] = y5;
}

int triviumThreeEnumuration(vector<int> flag, int evalNumRounds, map<bitset<288>, int, cmpBitset288>& countingBox, int threadNumber, int target = 0, struct twoStage opt = { false, 0, });

class threeEnumuration : public GRBCallback
{
public:
    vector<int> flag;
    vector<vector<GRBVar>> s;
    int target;
    map<bitset<288>, int, cmpBitset288>* countingBox;
    int threadNumber;
    threeEnumuration(vector<int> xflag, vector<vector<GRBVar>> xs, int xtarget, map<bitset<288>, int, cmpBitset288>* xcountingBox, int xthreadNumber)
    {
        flag = xflag;
        s = xs;
        target = xtarget;
        countingBox = xcountingBox;
        threadNumber = xthreadNumber;
    }
protected:
    void callback()
    {
        if (where == GRB_CB_MIPSOL)
        {
            int evalNumRounds = s.size() - 1;
            int divRound = evalNumRounds / 2;

            // store found solution into trail
            vector<bitset<288>> trail(evalNumRounds + 1);
            for (int r = 0; r <= evalNumRounds; r++)
            {
                for (int i = 0; i < 288; i++)
                {
                    if (round(getSolution(s[r][i])) == 1)  trail[r][i] = 1;
                    else  trail[r][i] = 0;
                }
            }

            // 2nd stage
            int solCnt = triviumThreeEnumuration(flag, evalNumRounds, *countingBox, threadNumber, target, { true, divRound, trail });

            int solTotal = 0;
            auto it = (*countingBox).begin();
            while (it != (*countingBox).end())
            {
                solTotal += (*it).second;
                it++;
            }
            // remove
            GRBLinExpr addCon = 0;
            for (int i = 0; i < 288; i++) {
                if (round(getSolution(s[divRound][i])) == 1)
                    addCon += (1 - s[divRound][i]);
                else
                    addCon += s[divRound][i];
            }
            addLazy(addCon >= 1);
        }
    }
};

int triviumThreeEnumuration(vector<int> flag, int evalNumRounds, map<bitset<288>, int, cmpBitset288>& countingBox, int threadNumber, int target, struct twoStage opt)
{

    GRBEnv env = GRBEnv();
    env.set(GRB_IntParam_LogToConsole, 0);
    env.set(GRB_IntParam_Threads, threadNumber);
    env.set(GRB_IntParam_MIPFocus, GRB_MIPFOCUS_BESTBOUND);
    //env.set(GRB_DoubleParam_TimeLimit, 3600 * 3);

    if ((opt.useTwoStage == true) && (opt.hint.size() == 0))
    {
        env.set(GRB_IntParam_LazyConstraints, 1);
    }
    else
    {
        env.set(GRB_IntParam_PoolSearchMode, 2);
        env.set(GRB_IntParam_PoolSolutions, 2000000000);
        env.set(GRB_DoubleParam_PoolGap, GRB_INFINITY);
    }
    GRBModel model = GRBModel(env);

    // Create variables
    vector<vector<GRBVar>> s(evalNumRounds + 1, vector<GRBVar>(288));
    for (int i = 0; i < 288; i++)
    {
        s[0][i] = model.addVar(0, 1, 0, GRB_BINARY);
    }

    if (pattern == 1)
    {
        // Const 0, constraint
        GRBLinExpr key_sum;
        for (int i = 0; i < 288; i++)
        {
            if (flag[i] == 0)  // Const 0, constraint
                model.addConstr(s[0][i] == 0);
            else if (flag[i] == 2)  // IV constraint
                model.addConstr(s[0][i] == 1);
            else if (flag[i] == 3)  // key constraint
                key_sum += s[0][i];
        }
        model.addConstr(key_sum == 1);
    }

    if (pattern == 2)
    {
        // Const 0, constraint
        for (int i = 0; i < 288; i++)
        {
            if (flag[i] == 0)  // Const 0, constraint
                model.addConstr(s[0][i] == 0);
            else if (flag[i] == 2)  // IV constraint
                model.addConstr(s[0][i] == 1);
        }
    }

    // Round function
    for (int r = 0; r < evalNumRounds; r++)
    {
        vector<GRBVar> tmp = s[r];
        triviumCoreThree(model, tmp, 65, 170, 90, 91, 92);
        triviumCoreThree(model, tmp, 161, 263, 174, 175, 176);
        triviumCoreThree(model, tmp, 242, 68, 285, 286, 287);
        for (int i = 0; i < 288; i++)
            s[r + 1][(i + 1) % 288] = tmp[i];
    }
    int loc[6] = { 65,92,161,176,242,287 };
    // Output constraint
    if (target == 0)
    {
        GRBLinExpr ks = 0;
        for (int i = 0; i < 288; i++)
            if ((i == 65) || (i == 92) || (i == 161) || (i == 176) || (i == 242) || (i == 287))
                ks += s[evalNumRounds][i];
            else
                model.addConstr(s[evalNumRounds][i] == 0);
        model.addConstr(ks == 1);
    }
    else if (target <= 6)
    {
        for (int i = 0; i < 288; i++)
        {
            if (i == loc[target - 1])
                model.addConstr(s[evalNumRounds][i] == 1);
            else
                model.addConstr(s[evalNumRounds][i] == 0);
        }
    }


    GRBLinExpr sumKey = 0;
    for (int i = 0; i < 80; i++) {
        sumKey += s[0][i];
    }
    model.setObjective(sumKey, GRB_MAXIMIZE);

    if (opt.useTwoStage == true && opt.hint.size() > 0)
    {
        // fix
        for (int i = 0; i < 288; i++) {
            if (opt.hint[opt.divRound][i] == 1)
                model.addConstr(s[opt.divRound][i] == 1);
            else
                model.addConstr(s[opt.divRound][i] == 0);
        }
        // hint
        for (int r = 0; r < evalNumRounds; r++)
        {
            for (int i = 0; i < 288; i++)
            {
                if (opt.hint[r][i] == 1)
                    s[r][i].set(GRB_DoubleAttr_Start, 1);
                else
                    s[r][i].set(GRB_DoubleAttr_Start, 0);
            }
        }
    }

    // Solve
    model.update();
    if (opt.useTwoStage == true && opt.hint.size() == 0)
    {
        threeEnumuration cb = threeEnumuration(flag, s, target, &countingBox, threadNumber);
        model.setCallback(&cb);
        model.optimize();
    }
    else
        model.optimize();

    int solCount = model.get(GRB_IntAttr_SolCount);


    if (opt.useTwoStage == true && opt.hint.size() > 0)
    {
        // check solution limit
        if (solCount >= 2000000000)
        {
            cerr << "Number of solutions is too large" << endl;
            exit(0);
        }
        // store the information about solutions
        for (int i = 0; i < solCount; i++)
        {
            model.set(GRB_IntParam_SolutionNumber, i);
            bitset<288> tmp;
            for (int j = 0; j < 288; j++)
            {
                if (round(s[0][j].get(GRB_DoubleAttr_Xn)) == 1) tmp[j] = 1;
                else tmp[j] = 0;
            }
            countingBox[tmp]++;
        }
        return solCount;
    }
    else
    {
        // check solution limit
        if (solCount >= 2000000000)
        {
            cerr << "Number of solutions is too large" << endl;
            exit(0);
        }

        // store the information about solutions
        for (int i = 0; i < solCount; i++)
        {
            model.set(GRB_IntParam_SolutionNumber, i);
            bitset<288> tmp;
            for (int j = 0; j < 288; j++)
            {
                if (round(s[0][j].get(GRB_DoubleAttr_Xn)) == 1)
                    tmp[j] = 1;
                else
                    tmp[j] = 0;
            }
            countingBox[tmp]++;
        }
    }

    //result
    if (model.get(GRB_IntAttr_Status) == GRB_INFEASIBLE)
        return -1;
    else if (model.get(GRB_IntAttr_Status) == GRB_OPTIMAL)
    {
        int upperBound = round(model.get(GRB_DoubleAttr_ObjVal));
        return upperBound;
    }
    else
    {
        cout << model.get(GRB_IntAttr_Status) << endl;
        return -2;
    }
    return -1;
}

void recover_supperpoly(int pt, uint8_t cube[], int dim, int evalNumRounds, int threadNumber)
{
    // constant (secret 3, active 2, const 1, const 0)
    vector<int> flag(288, 0);
    for (int i = 0; i < 80; i++)
        flag[i] = 3;
    for (int i = 0; i < dim; i++)
        flag[93 + cube[i]] = 2;
    flag[285] = 1;
    flag[286] = 1;
    flag[287] = 1;

    map<bitset<288>, int, cmpBitset288> countingBox;
    clock_t starttime, finishtime;
    starttime = clock();
    int loc[6] = { 65,92,161,176,242,287 };
    for (int i = 1; i <= 6; i++)
    {
        cout << "Target s" << loc[i - 1] + 1 << endl;
        triviumThreeEnumuration(flag, evalNumRounds, countingBox, threadNumber, i, { true,0, });


        if (pattern == 2)
        {
            for (int j = 0; j < 80; j++)
            {
                if (special_keys[pt][j] == 1)
                {
                    auto it = countingBox.begin();
                    while (it != countingBox.end())
                    {
                        if (((*it).second % 2) == 1)
                        {
                            bitset<288> tmp = (*it).first;
                            if (tmp[j] == 1 && tmp.count() > 1 + dim)
                            {
                                special_keys[pt][j] = 0;
                                break;
                            }
                        }
                        it++;
                    }
                }
            }

            if (special_keys[pt].count() == 0)
            {
                FLAG = 0;
                break;
            }
        }

    }
    finishtime = clock();

    if (FLAG == 1)
    {
        map<bitset<288>, int, cmpBitset288> countingBox2;
        auto it = countingBox.begin();
        while (it != countingBox.end())
        {
            bitset<288> tmp = (*it).first;
            for (int i = 0; i < dim; i++)
                tmp[93 + cube[i]] = 0;
            tmp[285] = 0;
            tmp[286] = 0;
            tmp[287] = 0;
            countingBox2[tmp] += (*it).second;
            it++;
        }
        ofstream results;
        results.open("results.txt", ios_base::app);
        results << "- Cube(" << dim << "): ";
        for (int i = 0; i < dim; i++)
            results << int(cube[i]) << ",";
        results << endl;
        results << "Usetime: " << (double)(finishtime - starttime) / CLOCKS_PER_SEC << endl;
        //results << countingBox.size() << " solutions are found" << endl;
        auto it2 = countingBox2.begin();
        while (it2 != countingBox2.end()) {
            if (((*it2).second % 2) == 1) {
                bitset<288> tmp = (*it2).first;
                for (int i = 0; i < 80; i++) {
                    if (tmp[i] == 1)
                        results << "k" << i;
                }
                results << " + ";
            }
            it2++;
        }
        results << endl;

        results.close();
    }
    
}


int main()
{
    int evalNumRounds = 820;
    int threadNumber = 40;
    pattern = 2;
    // If pattern=1, only recover the linear terms of these cubes;
    // If pattern=2, then we know that the linear term recover the superpolies.

    uint8_t cube[10][50] =
    {
        {0,1,2,3,4,6,8,10,11,12,13,14,15,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,8,9,10,11,12,13,14,15,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,23,24,25,26,27,28,29,30,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,19,21,23,24,25,26,27,28,29,30,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,36,39,40,41,46,49,51,52,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,24,25,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,24,25,26,27,28,29,30,31,32,34,36,39,40,41,42,46,49,51,52,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,24,25,26,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,63,66,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,21,24,25,26,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,53,54,55,58,61,63,66,69,72,74,76,78},
        {0,1,2,3,4,6,7,8,9,10,11,12,14,15,17,18,19,21,23,24,25,26,27,28,29,30,31,32,34,36,38,39,40,41,42,46,49,51,52,53,54,55,58,61,66,69,72,74,76,78},
    };

    
    if (pattern == 2)
    {
        bitset<80> special_key;
        ifstream file("linearkey.txt", ios::in);
        char buf[100] = { 0 };
        int term[80] = { 0 };
        int term_dim, i;
        while (file.getline(buf, sizeof(buf)))
        {
            i = 0;
            term_dim = 0;
            while (buf[i] != '\0')
            {
                term[term_dim] = (buf[i] - '0') * 10 + (buf[i + 1] - '0');
                term_dim++;
                i = i + 3;
            }

            for (int kl = 0; kl < 80; kl++)
            {
                special_key[kl] = 0;
            }

            for (int kl = 0; kl < term_dim; kl++)
            {
                special_key[term[kl]] = 1;
            }
            special_keys.push_back(special_key);
        }

        file.close();
    }
    

    for (int pt = 0; pt < 10; pt++)
    {
        FLAG = 1;
        cout << "NO. " << pt + 1 << endl;
        recover_supperpoly(pt, cube[pt], 50, evalNumRounds, threadNumber);
    }

    system("pause");
}

