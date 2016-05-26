module incometax

model

  entity Income {
    name                : String  = "Untitled" (default)
    monthlySalary       : Float
    holidayAllowance    : Float   = 8.0 (default)
    thirteenthMonth     : Boolean = false (default)
    leaseCarPrice       : Float?
    leaseCarPercent     : Float?
    leaseCarAddition    : Float?  = leaseCarPrice * leaseCarPercent / 100.0
    grossSalary         : Float   = monthlySalary * (1.0 + holidayAllowance / 100.0 + (if(thirteenthMonth) 1.0 / 12.0 else 0.0))
    grossSalaryYear     : Float   = grossSalary * 12.0
    taxableIncome       : Float   = grossSalaryYear + (leaseCarAddition <+ 0.0)
    taxBracket1         : Float   = 19922.0
    taxRate1            : Float   = 36.55 / 100.0
    taxBracket2         : Float   = 33715.0
    taxRate2            : Float   = 40.15 / 100.0
    taxBracket3         : Float   = 66421.0
    taxRate3            : Float   = 40.15 / 100.0
    taxRate4            : Float   = 52.0 / 100.0
    salaryBracket1      : Float   = min(taxableIncome ++ taxBracket1)
    salaryBracket2      : Float   = max(0.0 ++ min(taxableIncome ++ taxBracket2) - taxBracket1)
    salaryBracket3      : Float   = max(0.0 ++ min(taxableIncome ++ taxBracket3) - taxBracket2)
    salaryBracket4      : Float   = max(0.0 ++ taxableIncome - taxBracket3)
    incomeTax           : Float   =
      salaryBracket1 * taxRate1 + salaryBracket2 * taxRate2 + salaryBracket3 * taxRate3 +
      salaryBracket4 * taxRate4
    gernalTaxDiscount   : Float   =
      switch {
        case taxableIncome < 19222.0 => 2242.0
        case taxableIncome < 66417.0 => 2242.0 - 0.04822 * (taxableIncome - 19922.0)
        default => 0.0
      }
    employedTaxDiscount : Float   =
      switch {
        case taxableIncome < 9147.0 => 0.0193 * taxableIncome
        case taxableIncome < 19758.0 => 146.0 + 0.27698 * (taxableIncome - 9147.0)
        case taxableIncome < 34015.0 => 3103.0
        case taxableIncome < 111590.0 => 3103.0 - 0.04 * (taxableIncome - 34015.0)
        default => 0.0
      }
    tax                 : Float   = incomeTax - gernalTaxDiscount - employedTaxDiscount
    netSalaryYear       : Float   = grossSalaryYear - tax
    netSalary           : Float   = netSalaryYear / 12.0
    summary             : String  =
      name + " has a gross salary of " + grossSalary as String + " per month and a net salary of " +
      netSalary as String +
      " per month" +
      (if(count(leaseCarPrice) > 0) " with a lease car" else "") +
      "."
  }

data

  phpProgrammer: Income {
    name = "PHP programmer"
    monthlySalary = 2800.0
    holidayAllowance = 0.0
  }
  phdStudent: Income {
    name = "PhD Student"
    monthlySalary = 2500.0
    thirteenthMonth = true
  }
  seniorDeveloper: Income {
    name = "Senior Developer"
    monthlySalary = 4000.0
    leaseCarPrice = 17000.0
    leaseCarPercent = 21.0
  }

execute

  phpProgrammer.summary
  phdStudent.summary
  seniorDeveloper.summary
