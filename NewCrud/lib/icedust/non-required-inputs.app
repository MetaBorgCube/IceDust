module lib/icedust/non-required-inputs

section int-input

override template input( i: ref Int ){
  var req := getRequestParameter( id )

  request var errors: [String] := null

  if( errors != null && errors.length > 0 ){
    errorTemplateInput( errors ){
      inputIntInternal( i, id )[ all attributes ]
    }
    validate{ getPage().enterLabelContext( id ); }
    elements
    validate{ getPage().leaveLabelContext(); }
  }
  else{
    inputIntInternal( i, id )[ all attributes ]
    validate{ getPage().enterLabelContext( id ); }
    elements
    validate{ getPage().leaveLabelContext(); }
  }
  validate{
    if( req != null && req != "" ){
      if( /-?\d+/.match( req ) ){
        if( req.parseInt() == null ){
          errors := [ "Outside of possible number range" ];
        }
      }
      else{
        errors := [ "Not a valid number" ];
      }
    }
    if( errors == null ){ // if no wellformedness errors, check datamodel validations
      errors := i.getValidationErrors();
      errors.addAll( getPage().getValidationErrorsByName( id ) ); //nested validate elements
    }
    errors := handleValidationErrors( errors );
  }
}

override template inputIntInternal( i: ref Int, tname: String ){
  var req := getRequestParameter( tname )
  <input
    if( getPage().inLabelContext() ){
      id = getPage().getLabelString()
    }
    name = tname
    if( req != null ){
      value = req
    }
    else{
      value = i
    }
    inputInt attributes
    all attributes
  />
  databind{
    if( req != null ){
      i := req.parseInt();
    } else {
      i := null;
    }
  }
}

section float-input

override template input( i: ref Float ){
  var req := getRequestParameter( id )

  request var errors: [String] := null

  if( errors != null ){
    errorTemplateInput( errors ){
      inputFloatInternal( i, id )[ all attributes ]
    }
    validate{ getPage().enterLabelContext( id ); }
    elements
    validate{ getPage().leaveLabelContext(); }
  }
  else{
    inputFloatInternal( i, id )[ all attributes ]
    validate{ getPage().enterLabelContext( id ); }
    elements
    validate{ getPage().leaveLabelContext(); }
  }
  validate{
    if( req != null && req != ""){
      if(   /-?\d\d*\.\d*E?\d*/.match( req )
         || /-?\d\d*E?\d*/.match( req )
         || /-?\.\d\d*E?\d*/.match( req )
      ){
        var f: Float := req.parseFloat();
        if( f == null ){
          errors := [ "Not a valid decimal number" ];
        }
      }
      else{
        errors := [ "Not a valid decimal number" ];
      }
    }
    if( errors == null ){ // if no wellformedness errors, check datamodel validations
      errors := i.getValidationErrors();
      errors.addAll( getPage().getValidationErrorsByName( id ) ); //nested validate elements
    }
    errors := handleValidationErrors( errors );
  }
}

override template inputFloatInternal( i: ref Float, tname: String ){
  var req := getRequestParameter( tname )
  <input
    if( getPage().inLabelContext() ){
      id = getPage().getLabelString()
    }
    name = tname
    if( req != null ){
      value = req
    }
    else{
      value = i
    }
    inputFloat attributes
    all attributes
  />

  databind{
    if( req != null ){
      i := req.parseFloat();
    } else {
      i := null;
    }
  }
}


