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

section bool-input

override template output( b: Bool ){
  if(b == null) {
    "null"
  } else {
    <input
      type = "checkbox"
      if( b ){
       checked = "true"
      }
      disabled = "true"
      all attributes
    />
  }
}

template inputNonRequiredBool( b: ref Bool ){
  request var errors: [String] := null // request var keeps its value, even when validation fails (regular var is reset when validation fails)

  if( errors != null && errors.length > 0 ){
    errorTemplateInput( errors ){
      inputNonRequiredBoolInternal( b, id )[ all attributes ]  // use same id so the inputs are updated in both cases
      validate{ getPage().enterLabelContext( id ); }
      elements
      validate{ getPage().leaveLabelContext(); }
    }
  }
  else{
    inputNonRequiredBoolInternal( b, id )[ all attributes ]
    validate{ getPage().enterLabelContext( id ); }
    elements
    validate{ getPage().leaveLabelContext(); }
  }
  validate{
    errors := b.getValidationErrors();
    errors.addAll( getPage().getValidationErrorsByName( id ) ); //nested validate elements
    errors := handleValidationErrors( errors );
  }
}

template inputNonRequiredBoolInternal( b: ref Bool, rname: String ){
  var rnamehidden := rname + "_isinput"

  <input type = "hidden" name=rname + "_isinput" />
  
  <div class="optionalBoolean non-required-bool"
  if( getPage().inLabelContext() ){
      id = getPage().getLabelString()
    }>
    <input
      type="radio"
      name=rname
      value="true"
      if(       getRequestParameter( rnamehidden ) != null
           && getRequestParameter( rname ) == "true"
        ||
              getRequestParameter( rnamehidden ) == null
           && b == true
      ){
        checked = "true"
      }
      inputBool attributes
      all attributes>"True"</input>
      
      <input
      type="radio"
      name=rname
      value="false"
      if(       getRequestParameter( rnamehidden ) != null
           && getRequestParameter( rname ) == "false"
        ||
              getRequestParameter( rnamehidden ) == null
           && b == false
      ){
        checked = "true"
      }
      inputBool attributes
      all attributes>"False"</input>
      
      <input
      type="radio"
      name=rname
      value="null"
      if(       getRequestParameter( rnamehidden ) != null
           && getRequestParameter( rname ) == "null"
        ||
              getRequestParameter( rnamehidden ) == null
           && b == null
      ){
        checked = "true"
      }
      inputBool attributes
      all attributes>"null"</input>
  </div>

  databind{
    var tmp: String := getRequestParameter( rname );
    var tmphidden := getRequestParameter( rnamehidden );
    if( tmphidden != null ){
      if( getRequestParameter( rname ) == "null" ){
        b := null;
      } else {
        if(getRequestParameter(rname) == "true") {
          b := true;
        }
        else{
          b := false;
        }
      }
    }
  }
}



