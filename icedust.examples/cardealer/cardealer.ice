module cardealer

model

  entity CarDealer {
    hasTransactions : Boolean = count(transactions) > 0
    maxAmount       : Int?    = max(transactions.amount)
  }
  
  relation CarDealer.transactions * <-> 1 Transaction.carDealer
  
  entity Transaction {
    amount : Int
  }
  
  relation CarDealer.products * <-> 1 Product
  
  entity Product {
    inStock       : Boolean = stockQuantity > 0 <+ false // (constraint)
    stockQuantity : Int?
    recalled      : Boolean = false (default)
    forSale       : Boolean
  }
  
  relation CarDealer.purchaseOrders <-> 1 PurchaseOrder
  
  entity PurchaseOrder {
  
  }
  
  relation CarDealer.saleOrders <-> 1 SaleOrder
  
  entity SaleOrder {
    isPaid : Boolean = count(transaction)>0
  }
  
  relation SaleOrder ? <-> ? Transaction
  
  relation SaleOrder 1 <-> * Product
  
  relation CarDealer.productsForSale = products.filter(x => x.forSale) <-> Product.carDealerForSale
  
  relation CarDealer.soldProducts = saleOrders.product <-> Product.carDealerSold //FIXME: must be unique
