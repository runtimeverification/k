from graphene import Enum, Interface, NonNull
from graphene.types import Scalar


class ProcessID(Scalar):
    ...


class ProcessStatus(Enum):
    PENDING = 'PENDING'
    RUNNING = 'RUNNING'
    DONE = 'DONE'


class Process(Interface):
    id = NonNull(ProcessID)
    status = NonNull(ProcessStatus)
