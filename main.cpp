#include <iostream>
#include <z3++.h>
#include <z3.h>
#include <assert.h>
#include <vector>

#define POLY UINT64_C(0x42f0e1eba9ea3693)
#define TOP UINT64_C(0x8000000000000000)

z3::expr long_and(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, 64);

    return ex & cpc;
}

z3::expr unsigned_gt(z3::expr ex, uint64_t in)
{
    z3::expr cpc = ex.ctx().bv_val((unsigned long long)in, 64);

    return z3::to_expr(ex.ctx(), Z3_mk_bvugt(ex.ctx(), ex, cpc));
}

uint64_t get_z3_interp(z3::solver& s, const std::string& n1)
{
    z3::model m = s.get_model();

    z3::func_decl d0 = m.get_const_decl(0);

    assert(d0.name().str() == n1);

    z3::expr e0 = m.get_const_interp(d0);

    uint64_t s0 = -1;

    Z3_get_numeral_uint64(s.ctx(), e0, &s0);

    return s0;
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

        std::cout << "VUP " << std::hex << shifted_up << std::endl;

        //uint64_t what = ((uint64_t)(*buf)) << 56;

        buf++;

        //std::cout << "VUP " << std::hex << what << std::endl;

        crc ^= shifted_up;

        std::cout << "FCRC " << std::hex << crc << std::endl;

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
    //solve.add(dummy == fin);

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

    for(int i=0; i < v2.size(); i++)
    {
        res[i] ^= v2[i];
    }

    return res;
}

int main()
{
    assert(crc64_ecma182_orig(0, "che", 3) == 0x824f3151871f12a7);


    //auto che_orig = crc64_ecma182_orig(0, "che", 3);
    z3_crc("che");

    /*auto Che_orig = crc64_ecma182_orig(0, "Che", 3);

    uint64_t res = che_orig ^ Che_orig;

    std::string v1 = "che";
    std::string v2 = "Che";

    std::string xord = xor_strings(v1, v2);

    uint64_t crc_xord = crc64_ecma182_orig(0, xord.c_str(), xord.size());

    std::cout << "R " << std::hex << res << " THEN " << crc_xord << std::endl;*/

    return 0;
}
