setDerived("employedTaxDiscount",function() {
      return conditional_One_One_One(lt_Float(get("taxableIncome"),9147.0),mul_Float(0.0193,get("taxableIncome")),conditional_One_One_One(lt_Float(get("taxableIncome"),19758.0),plus_Float(146.0,mul_Float(0.27698,minus_Float(get("taxableIncome"),9147.0))),conditional_One_One_One(lt_Float(get("taxableIncome"),34015.0),3103.0,conditional_One_One_One(lt_Float(get("taxableIncome"),111590.0),minus_Float(3103.0,mul_Float(0.04,minus_Float(get("taxableIncome"),34015.0))),0.0))));
  });

setDerived("gernalTaxDiscount",function() {
      return conditional_One_One_One(lt_Float(get("taxableIncome"),19222.0),2242.0,conditional_One_One_One(lt_Float(get("taxableIncome"),66417.0),minus_Float(2242.0,mul_Float(0.04822,minus_Float(get("taxableIncome"),19922.0))),0.0));
  });

setDerived("grossSalary",function() {
      return mul_Float(get("monthlySalary"),plus_Float(plus_Float(1.0,div_Float(get("holidayAllowance"),100.0)),conditional_One_One_One(get("thirteenthMonth"),div_Float(1.0,12.0),0.0)));
  });

setDerived("grossSalaryYear",function() {
      return mul_Float(get("grossSalary"),12.0);
  });

setDerived("holidayAllowance",function() {
      return 8.0;
  });

setDerived("incomeTax",function() {
      return plus_Float(plus_Float(plus_Float(mul_Float(get("salaryBracket1"),get("taxRate1")),mul_Float(get("salaryBracket2"),get("taxRate2"))),mul_Float(get("salaryBracket3"),get("taxRate3"))),mul_Float(get("salaryBracket4"),get("taxRate4")));
  });

setDerived("leaseCarAddition",function() {
      return div_Float(mul_Float(get("leaseCarPrice"),get("leaseCarPercent")),100.0);
  });

setDerived("name",function() {
      return "Untitled";
  });

setDerived("netSalary",function() {
      return div_Float(get("netSalaryYear"),12.0);
  });

setDerived("netSalaryYear",function() {
      return minus_Float(get("grossSalaryYear"),get("tax"));
  });

setDerived("salaryBracket1",function() {
      return min_Float(merge_One_One(get("taxableIncome"),get("taxBracket1")));
  });

setDerived("salaryBracket2",function() {
      return max_Float(merge_One_One(0.0,minus_Float(min_Float(merge_One_One(get("taxableIncome"),get("taxBracket2"))),get("taxBracket1"))));
  });

setDerived("salaryBracket3",function() {
      return max_Float(merge_One_One(0.0,minus_Float(min_Float(merge_One_One(get("taxableIncome"),get("taxBracket3"))),get("taxBracket2"))));
  });

setDerived("salaryBracket4",function() {
      return max_Float(merge_One_One(0.0,minus_Float(get("taxableIncome"),get("taxBracket3"))));
  });

setDerived("summary",function() {
      return plus_String(plus_String(plus_String(plus_String(plus_String(plus_String(plus_String(get("name")," has a gross salary of "),asString(get("grossSalary")))," per month and a net salary of "),asString(get("netSalary")))," per month"),conditional_One_One_One(gt_Integer(count(get("leaseCarPrice")),0)," with a lease car","")),".");
  });

setDerived("tax",function() {
      return minus_Float(minus_Float(get("incomeTax"),get("gernalTaxDiscount")),get("employedTaxDiscount"));
  });

setDerived("taxableIncome",function() {
      return plus_Float(get("grossSalaryYear"),choice_One_One(get("leaseCarAddition"),0.0));
  });

setDerived("taxBracket1",function() {
      return 19922.0;
  });

setDerived("taxBracket2",function() {
      return 33715.0;
  });

setDerived("taxBracket3",function() {
      return 66421.0;
  });

setDerived("taxRate1",function() {
      return div_Float(36.55,100.0);
  });

setDerived("taxRate2",function() {
      return div_Float(40.15,100.0);
  });

setDerived("taxRate3",function() {
      return div_Float(40.15,100.0);
  });

setDerived("taxRate4",function() {
      return div_Float(52.0,100.0);
  });

setDerived("thirteenthMonth",function() {
      return false;
  });