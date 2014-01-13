\name{orca}
\alias{count4}
\alias{count5}
\alias{ecount4}
\alias{ecount5}
\title{Orbit counting} 

\description{
Count the node (edge) orbits in 4- or 5- node graphlets for all nodes (edges) in the given graph.
}

\usage{
count4(graph)
count5(graph)
ecount4(graph)
ecount5(graph)
}
\arguments{
  \item{graph}{A graph given as a nx2 edge matrix, a data frame with edges or a graphNEL from the package 'graph'.  Nodes are given by indices that start with 1.
}
}
%% \details{}
\value{
An integer matrix, with the rows corresponding to graph nodes (edges) and the columns corresponding to orbit counts.
}
\references{
Tomaz Hocevar, Janez Demsar (2014): A combinatorial approach to graphlet counting. Bioinformatics.
}
\author{
Tomaz Hocevar and Janez Demsar}
\note{
%%  ~~further notes~~
}

%% ~Make other sections like Warning with \section{Warning }{....} ~

\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
}
\examples{
library(orca)
data("randomNetwork")

count4(randomNetwork)
}
% Add one or more standard keywords, see file 'KEYWORDS' in the
% R documentation directory.
\keyword{graphs}
