function tryRenameFunctionName(fn, name){
	var descriptor = Object.getOwnPropertyDescriptor(fn, 'name');
	if(descriptor.configurable){
		Object.defineProperty(fn, 'name', {value: name});
	}
}

module.exports = {
	tryRenameFunctionName: tryRenameFunctionName
};