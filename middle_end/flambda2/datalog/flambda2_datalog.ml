module Datalog = struct
  type nil = Heterogenous_list.nil

  module Column = Column
  include Datalog
end
