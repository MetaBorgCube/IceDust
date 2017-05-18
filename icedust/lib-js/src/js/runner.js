import {
  emptyState,
  init,
  execute
} from './generated';

let {state, ids} = init(emptyState);
let result;
({state, result} = execute(state, ids));

for(let r of result){
  console.log(r)
}
