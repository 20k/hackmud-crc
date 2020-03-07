#include <iostream>
#include <z3++.h>
#include <z3.h>
#include <assert.h>
#include <vector>
#include <string.h>

#define POLY UINT64_C(0x42f0e1eba9ea3693)
#define TOP UINT64_C(0x8000000000000000)

z3::expr long_and(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, ex.get_sort().bv_size());

    return ex & cpc;
}

z3::expr unsigned_gt(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, ex.get_sort().bv_size());

    return z3::to_expr(ex.ctx(), Z3_mk_bvugt(ex.ctx(), ex, cpc));
}

z3::expr unsigned_gte(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, ex.get_sort().bv_size());

    return z3::to_expr(ex.ctx(), Z3_mk_bvuge(ex.ctx(), ex, cpc));
}

z3::expr unsigned_lt(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, ex.get_sort().bv_size());

    return z3::to_expr(ex.ctx(), Z3_mk_bvult(ex.ctx(), ex, cpc));
}

z3::expr unsigned_lte(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, ex.get_sort().bv_size());

    return z3::to_expr(ex.ctx(), Z3_mk_bvule(ex.ctx(), ex, cpc));
}

uint64_t get_z3_interp(z3::solver& s, const std::string& n1)
{
    z3::model m = s.get_model();

    int num_consts = m.num_consts();

    for(int i=0; i < num_consts; i++)
    {
        z3::func_decl d0 = m.get_const_decl(i);

        //assert(d0.name().str() == n1);

        if(d0.name().str() != n1)
            continue;

        z3::expr e0 = m.get_const_interp(d0);

        uint64_t s0 = -1;

        Z3_get_numeral_uint64(s.ctx(), e0, &s0);

        return s0;
    }

    assert(false);
    return -1;
}

uint64_t get_z3_interp(z3::expr e)
{
    uint64_t s0 = -1;

    Z3_get_numeral_uint64(e.ctx(), e, &s0);

    return s0;
}

z3::expr long_xor(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, 64);

    //std::cout << std::hex << "FA " << get_z3_interp(ex) << " FB " << get_z3_interp(cpc) << std::endl;

    return z3::to_expr(ex.ctx(), Z3_mk_bvxor(ex.ctx(), ex, cpc));
    //return ex ^ cpc;
}

z3::expr long_xor(z3::expr ex, z3::expr ex2)
{
    //std::cout << "shifted " << get_z3_interp(ex2) << " two " << get_z3_interp(ex) << std::endl;

    return z3::to_expr(ex.ctx(), Z3_mk_bvxor(ex.ctx(), ex, ex2));

    //return ex ^ ex2;
}

z3::expr left_shift(z3::expr ex, uint64_t by)
{
    z3::expr cst = ex.ctx().bv_val((unsigned long long)by, ex.get_sort().bv_size());

    return z3::to_expr(ex.ctx(), Z3_mk_bvshl(ex.ctx(), ex, cst));
}

#define ZCYCLE crc = z3::ite(unsigned_gt(long_and(crc, TOP), 0), long_xor(left_shift(crc, 1), POLY), left_shift(crc, 1))

// initial crc is 0
uint64_t crc64_ecma182_orig(uint64_t crc,  const char *buf, size_t len)
{
    while (len--) {
        uint64_t shifted_up = ((uint64_t)*buf) << 56;

        //std::cout << "VUP " << std::hex << shifted_up << std::endl;

        //uint64_t what = ((uint64_t)(*buf)) << 56;

        buf++;

        //std::cout << "VUP " << std::hex << what << std::endl;

        crc ^= shifted_up;

        //std::cout << "FCRC " << std::hex << crc << std::endl;

        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
        crc = crc & TOP ? (crc << 1) ^ POLY : crc << 1;
    }
    return crc;
}

z3::expr z3_crc_impl(z3::context& ctx, const std::vector<z3::expr>& in)
{
    int len = in.size();

    unsigned long long val = 0;

    z3::expr crc = ctx.bv_val(val, 64);

    int idx = 0;

    while(len--)
    {
        z3::expr shifted = left_shift(in[idx], 56);

        crc = long_xor(crc, shifted);

        idx++;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
        ZCYCLE;
    }

    return crc;
}

z3::expr is_eq(z3::expr one, z3::expr two)
{
    return z3::expr(one.ctx(), Z3_mk_eq(one.ctx(), one, two));
}

z3::expr is_eq(z3::expr one, bool two)
{
    return is_eq(one, one.ctx().bv_val((uint64_t)two, 64));
}

void z3_crc(const std::string& str)
{
    z3::context ctx;
    z3::solver solve(ctx);
    //z3::expr

    std::vector<z3::expr> zexpr;

    int idx = 0;

    for(auto& i : str)
    {
        //std::string name = "c" + std::to_string(idx);

        //zexpr.emplace_back(ctx.bv_const(name.c_str(), 8));

        zexpr.emplace_back(ctx.bv_val((unsigned long long)i, 64));

        idx++;
    }

    auto res = z3_crc_impl(ctx, zexpr);

    z3::expr dummy = ctx.bv_const("out", 64);

    z3::expr fin = ctx.bv_val(UINT64_C(0x824f3151871f12a7), 64);

    solve.add(dummy == res);
    solve.add(dummy == fin);

    solve.check();

    //std::cout << "VAL " << std::hex << res << std::endl;

    std::cout << solve.get_model() << std::endl;

    /*{
        z3::expr expr = ctx.bv_val((unsigned long long)0x63, 64);

        z3::expr next = left_shift(expr, 56);

        z3::expr dummy = ctx.bv_const("out", 64);

        solve.add(dummy == next);

        solve.check();

        std::cout << get_z3_interp(next) << std::endl;
    }*/
}

void z3_crc_reverse(uint64_t cst)
{
    //int len = 7;

    for(int len=2; len < 20; len++)
    {
        z3::context ctx;
        z3::solver solve(ctx);

        std::vector<z3::expr> zexpr;
        std::vector<z3::expr> excluded;

        for(int i=0; i < len; i++)
        {
            std::string name = "c" + std::to_string(i);

            z3::expr nexpr = ctx.bv_const(name.c_str(), 8);

            solve.add(unsigned_gte(nexpr, 48));
            //solve.add(unsigned_gte(nexpr, 65));
            solve.add(unsigned_lte(nexpr, 122));

            if(i < len / 2)
            {
                solve.add(unsigned_gte(nexpr, 95));
            }

            solve.add(nexpr != 58);
            solve.add(nexpr != 59);
            solve.add(nexpr != 60);
            solve.add(nexpr != 61);
            solve.add(nexpr != 62);
            solve.add(nexpr != 63);
            solve.add(nexpr != 64);
            solve.add(nexpr != 91);
            solve.add(nexpr != 92);
            solve.add(nexpr != 93);
            solve.add(nexpr != 94);
            solve.add(nexpr != 96);

            zexpr.emplace_back(nexpr);
        }

        std::string hint = "";

        for(int i=0; i < (int)hint.size() && i < len; i++)
        {
            solve.add(zexpr[i] == ctx.bv_val((uint8_t)hint[i], 8));
        }

        std::vector<z3::expr> extended;

        for(auto& i : zexpr)
        {
            extended.emplace_back(z3::expr(ctx, Z3_mk_zero_ext(ctx, 64-8, i)));
        }

        auto res = z3_crc_impl(ctx, extended);

        z3::expr fin = ctx.bv_val(cst, 64);

        solve.add(res == fin);

        while(1)
        {
            z3::check_result is_solved = solve.check();

            if(is_solved != z3::sat)
                break;

            //std::cout << solve.get_model() << std::endl;

            std::vector<uint64_t> vals;

            for(int i=0; i < len; i++)
            {
                std::string name = "c" + std::to_string(i);

                uint64_t val = get_z3_interp(solve, name);

                std::cout << (char)val;

                vals.push_back(val);
            }

            std::cout << std::endl;


            /*for(int i=0; i < zexpr.size(); i++)
            {
                solve.add(zexpr[i] != ctx.bv_val(vals[i], 64));
            }*/

            //return;

            //z3::expr root_and = is_eq(zexpr[0], ctx.bv_val(vals[0], 64));

            z3::expr root_and = zexpr[0] == ctx.bv_val((uint8_t)vals[0], 8);

            for(int i=1; i < (int)zexpr.size(); i++)
            {
                root_and = (root_and && (zexpr[i] == ctx.bv_val((uint8_t)vals[i], 8)));
                //root_and = (root_and && is_eq(zexpr[i], ctx.bv_val(vals[i], 64)));
            }

            solve.add(!root_and);

            //solve.add(fin == fin);
        }


        //break;
    }
}

void hackmud_crack()
{
    /*z3::context ctx;
    z3::solver solve(ctx);

    z3::expr a = ctx.bv_const("a", 32);
    z3::expr b = ctx.bv_const("b", 32);

    z3::sort bv_sort = ctx.bv_sort(32);

    z3::func_decl func = ctx.function("Testo", 1, &bv_sort, bv_sort);

    solve.add(func(func(a)) == a);
    solve.add(func(a) == b);

    solve.add(a != b);
    solve.check();

    std::cout << solve.get_model() << std::endl;*/
}

std::string xor_strings(const std::string& v1, const std::string& v2)
{
    std::string res = v1;

    assert(v1.size() == v2.size());

    for(int i=0; i < (int)v2.size(); i++)
    {
        res[i] ^= v2[i];
    }

    return res;
}

int main()
{
    assert(crc64_ecma182_orig(0, "che", 3) == 0x824f3151871f12a7);
    assert(crc64_ecma182_orig(0, "TecIYjwcPUy", strlen("TecIYjwcPUy")) == 0xad8bc39b0edec636);
    assert(crc64_ecma182_orig(0, "be7CE2QP40BH3ZHQ2kQm5W", strlen("be7CE2QP40BH3ZHQ2kQm5W")) == 0xad8bc39b0edec636 );
    assert(crc64_ecma182_orig(0, "login_is_false_MaciekP", strlen("login_is_false_MaciekP")) == 0xad8bc39b0edec636 );

    //ad8bc39b0edec636 login_is_false_MaciekP


    //auto che_orig = crc64_ecma182_orig(0, "che", 3);
    z3_crc("che");
    //z3_crc_reverse(0xad8bc39b0edec636);
    //z3_crc_reverse(0x6861a3661fff4586ll);

    std::vector<uint64_t> arr =
    {
        /*0x6861a3661fff4586ll,
        0x334c5c9bffd5886dll,
        0xc84ebcf63df0fbe4ll,
        0xb7a8d3dbcc26d6e9ll,
        0x1ad76a75301c3fcbll,
        0x2ec4a326cfeb6bebll,
        0xc025c245bd506dfbll,
        0xd7e35a4d9181635ell,
        0xd4603da01cae7b13ll,
        0xe3e559061e4ec5a6ll,
        0xe1c22e6031df5f9bll,
        0x6cc0334d8879887all,
        0x506c409e34ebcbd3ll,
        0x5cdcf1e26d5290eell,
        0x23fd58ea7a7ba63cll,*/

        0xe3e559061e4ec5a6

        //0xad8bc39b0edec636
    };

    for(auto& i : arr)
    {
        z3_crc_reverse(i);
        std::cout << "FROM " << std::hex << i << std::endl;
    }

    //z3_crc_reverse(0x824f3151871f12a7);

    /*auto Che_orig = crc64_ecma182_orig(0, "Che", 3);

    uint64_t res = che_orig ^ Che_orig;

    std::string v1 = "che";
    std::string v2 = "Che";

    std::string xord = xor_strings(v1, v2);

    uint64_t crc_xord = crc64_ecma182_orig(0, xord.c_str(), xord.size());

    std::cout << "R " << std::hex << res << " THEN " << crc_xord << std::endl;*/

    return 0;
}
